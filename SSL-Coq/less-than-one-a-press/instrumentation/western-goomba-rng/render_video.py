"""Presentation of the existing checked trace; no new physics or AI model.

Uses Pillow only. Terrain is a clipped view of the actual generated collision
mesh. The Goomba icon is schematic, anchored at each recorded feet position.
No ROM or emulator is run, modified, or reconstructed by this renderer.
"""
import argparse
import json
import math
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[2]
BASE_OUT = ROOT / 'build/instrumentation/western-goomba-rng/video'
parser=argparse.ArgumentParser()
parser.add_argument('--preview',action='store_true')
parser.add_argument('--home-range',action='store_true')
parser.add_argument('--direct-rim',action='store_true')
args=parser.parse_args()
if args.direct_rim: BASE_OUT=ROOT/'build/instrumentation/western-goomba-rng/elevator-analysis/video-direct'
DATA = json.loads((BASE_OUT / 'data.json').read_text())
OUT = BASE_OUT / 'home-range' if args.home_range and not args.direct_rim else BASE_OUT
ROWS = DATA['frames']
PAUSE=DATA['waypoint']['frame']-1
W, H = 1280, 800
BG, FG, MUTED = '#101c26', '#edf2f2', '#abbcc7'
AMBER, RED, BLUE = '#ffcc68', '#ee7766', '#75bfce'
MINT = '#8ed7ba'
FONT = Path('C:/Windows/Fonts/segoeui.ttf')
if not FONT.exists():
    FONT = Path('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf')
def font(size): return ImageFont.truetype(str(FONT), size)
F18, F20, F24, F30 = [font(n) for n in (18,20,24,30)]

# Orthographic cutaway. Y is vertical throughout; X/Z remain game coordinates.
CX, CZ, SCALE = -3550, 2350, .235
def project(p):
    x,y,z = p
    return (450 + SCALE*(.94*(x-CX)+.62*(z-CZ)),
            387 + SCALE*(.24*(x-CX)-.50*(z-CZ)-1.05*y))
def clipped(poly, axis, edge, greater):
    out=[]
    for a,b in zip(poly,poly[1:]+poly[:1]):
        ia=(a[axis]>=edge) if greater else (a[axis]<=edge)
        ib=(b[axis]>=edge) if greater else (b[axis]<=edge)
        if ia: out.append(a)
        if ia!=ib:
            t=(edge-a[axis])/(b[axis]-a[axis])
            out.append([a[k]+t*(b[k]-a[k]) for k in range(3)])
    return out
def clip_face(v):
    p=v
    for axis,low,high in ((0,-4300,-2800),(2,1300,3400),(1,-220,180)):
        if not p: break
        p=clipped(p,axis,low,True)
        if p:p=clipped(p,axis,high,False)
    return p
def normal(v):
    a,b,c=v
    u=[b[k]-a[k] for k in range(3)];w=[c[k]-a[k] for k in range(3)]
    return (u[1]*w[2]-u[2]*w[1],u[2]*w[0]-u[0]*w[2],u[0]*w[1]-u[1]*w[0])
def label(d,xy,text,fill=FG,f=F18,anchor=None):
    d.text(xy,text,font=f,fill=fill,anchor=anchor,stroke_width=2,stroke_fill=BG)
def star(d,p,r=8,color=RED):
    x,y=p
    pts=[(x+math.sin(i*math.pi/5)*(r if i%2==0 else r*.42),
          y-math.cos(i*math.pi/5)*(r if i%2==0 else r*.42)) for i in range(10)]
    d.polygon(pts,fill=color)
def ring(d,p,r=6,color=AMBER):
    x,y=p;d.ellipse((x-r,y-r,x+r,y+r),outline=color,width=2)
def dashed(d,points,color,width=2,period=8):
    for i,(a,b) in enumerate(zip(points,points[1:])):
        if i%period<period//2:d.line((a,b),fill=color,width=width)
def home_circle(projection):
    x,y,z=DATA['home']['center'];r=DATA['home']['radius']
    return [projection([x+r*math.cos(i*math.tau/240),y,z+r*math.sin(i*math.tau/240)]) for i in range(241)]

base=Image.new('RGB',(W,H),BG);d=ImageDraw.Draw(base)
d.text((32,20),'Western Goomba — direct approach to the original rim' if args.direct_rim else 'Western Goomba — the exact diagnostic path',font=F30,fill=FG)
d.text((32,61),'Recorded native positions • favorable RNG outcomes • reconstructed view',font=F20,fill=MUTED)
d.line((32,102,1248,102),fill='#304553',width=1)
d.text((32,119),'Home range and direct approach' if args.home_range else 'Collision-mesh cutaway',font=F20,fill=FG)
d.text((32,145),'Mint: 1,000-unit home threshold at Y=0  •  white: direct bearing' if args.home_range else 'Upper floors hidden; Goomba artwork is schematic.',font=F18,fill=MUTED)

polys=[]
for face in DATA['mesh']['faces']:
    n=normal(face['vertices'])
    if n[1]<0: continue  # ceilings are omitted in this cutaway
    poly=clip_face(face['vertices'])
    if len(poly)<3: continue
    center=[sum(p[k] for p in poly)/len(poly) for k in range(3)]
    sand=face['type'] in (33,34,35,36,37,38,39,44,45)
    if face['ordinal'] in (336,337): color=RED
    elif sand or (n[1]>0 and center[1]<-20):color='#9b8054'
    elif n[1]>0:color='#6c7a78' if center[1]<50 else '#9ea499'
    else:color='#495c64'
    # Painter order is a presentation choice; no collision query uses this.
    depth=-.34*center[0]+.66*center[2]+.7*center[1]
    polys.append((depth,poly,color))
for _,poly,color in sorted(polys,key=lambda x:x[0]):
    pts=[project(p) for p in poly]
    d.polygon(pts,fill=color)
    d.line(pts+[pts[0]],fill='#40545b',width=1)

start=project([-3638,0,1928]);target=project(DATA['originalRimTarget'])
waypoint=project(DATA['waypoint']['position'])
if args.home_range:
    dashed(d,home_circle(project),MINT,2)
    bearing=[project([-3638+567*i/100,0,1928]) for i in range(101)]
    dashed(d,bearing,FG,2,10)
    d.line((bearing[-1],target),fill=FG,width=1)
ring(d,start,7);label(d,(155,531),'Start  (-3638, 0, 1928)',AMBER)
d.line((start[0],start[1]+8,280,526),fill=AMBER,width=1)
star(d,target)
label(d,(635,475),'Original rim target',RED)
label(d,(635,499),'(-3071, 113, 1928)',RED)
d.line((target[0]+9,target[1],625,487),fill=RED,width=1)
ring(d,waypoint,7,BLUE)
label(d,(680,304),f'Update {PAUSE+1}',BLUE)
label(d,(680,328),'Outside the rim',BLUE)
d.line((waypoint[0]+9,waypoint[1],672,328),fill=BLUE,width=1)
wall=project([-3112,50,2240])
d.line((wall[0],wall[1],805,548),fill=RED,width=1)
label(d,(635,552),'Entry wall: Y=0…72',RED)
label(d,(635,576),'X=-3112',RED)
label(d,(470,612),'Lower sand pit', '#ddc39b')
label(d,(85,592),'Western corridor')

# Whole local neighborhood, static start markers only. None is a simulated actor.
d.line((917,115,917,643),fill='#304553',width=1)
d.text((943,119),'Nearby stock starts',font=F20,fill=FG)
d.text((943,146),'Context only — not simulated',font=F18,fill=MUTED)
def mini(p):
    return (964+(p[0]+4500)*.067, 187+(p[2]+2400)*.057)
for face in DATA['mesh']['faces']:
    n=normal(face['vertices'])
    if n[1]<=0 or max(p[1] for p in face['vertices'])>256:continue
    poly=face['vertices']
    for axis,low,high in ((0,-4500,-1000),(2,-2400,4200)):
        poly=clipped(poly,axis,low,True)
        if poly:poly=clipped(poly,axis,high,False)
        if not poly:break
    if len(poly)>2:
        color='#746748' if sum(p[1] for p in poly)/len(poly)<-20 else '#40545b'
        d.polygon([mini(p) for p in poly],fill=color)
for face in DATA['mesh']['faces']:
    v=face['vertices'];n=normal(v)
    if n[1]!=0 or min(p[1] for p in v)>256:continue
    for a,b in zip(v,v[1:]+v[:1]):
        if a[1]!=b[1] or a[1]>256:continue
        if all(-4500<=p[0]<=-1000 and -2400<=p[2]<=4200 for p in (a,b)):
            d.line((mini(a),mini(b)),fill='#93a298',width=1)
for obj in DATA['stockContext']:
    x,y=mini(obj['pos']);d.rectangle((x-4,y-4,x+4,y+4),outline=BLUE,width=2)
    if obj['name']=='Western Grindel':
        label(d,(x+14,y-10),'Grindel',BLUE)
    else:label(d,(x-15,y+12),'Southern Goomba',BLUE,anchor='mt')
mx,my=mini([-3638,0,1928]);ring(d,(mx,my),5,AMBER)
if args.home_range:dashed(d,home_circle(mini),MINT,1)
label(d,(mx+15,my-9),'This Goomba',AMBER)
d.text((943,579),'N  ↑     X →',font=F18,fill=MUTED)
d.text((943,607),'Z increases downward',font=F18,fill=MUTED)

d.line((32,650,1248,650),fill='#304553',width=1)
d.text((32,744),f"Static terrain • Mario fixed at {tuple(DATA['grantedMario'])} • other actors absent",font=F18,fill=MUTED)
d.text((32,770),'Cutaway and schematic Goomba; traced positions, not emulator footage. Home range is not a hard limit.' if args.home_range else 'This reconstructs the tested path. It is not an emulator recording or a complete gameplay route.',font=F18,fill=MUTED)

def goomba(draw,feet,row):
    x,y=feet
    # Feet stay attached to the recorded position; only cosmetic foot swing.
    swing=2*math.sin(row[0]*.5) if row[5]==0 else 0
    draw.ellipse((x-14,y-4+swing,x-1,y+2+swing),fill='#49301d',outline='#e9c894')
    draw.ellipse((x+1,y-4-swing,x+14,y+2-swing),fill='#49301d',outline='#e9c894')
    draw.ellipse((x-8,y-21,x+8,y-2),fill='#e4c391')
    draw.polygon([(x-19,y-17),(x-15,y-29),(x-8,y-37),(x+8,y-37),(x+15,y-29),(x+19,y-17)],fill='#a25f31',outline='#f1bb70')
    for ex in (x-7,x+7):
        draw.ellipse((ex-5,y-29,ex+5,y-16),fill='#f9f4e5')
        draw.ellipse((ex-1,y-25,ex+2,y-17),fill='#15202a')
    draw.line((x-12,y-30,x-2,y-26),fill='#201a16',width=3)
    draw.line((x+12,y-30,x+2,y-26),fill='#201a16',width=3)

def frame(index,hold=False):
    row=ROWS[index];im=base.copy();dr=ImageDraw.Draw(im)
    points=[project([r[1],r[2]+2,r[3]]) for r in ROWS[:index+1]]
    if len(points)>1:dr.line(points,fill=AMBER,width=3)
    ground=project([row[1],0,row[3]]);feet=project(row[1:4])
    dr.ellipse((ground[0]-12,ground[1]-4,ground[0]+12,ground[1]+4),fill='#25333a')
    if row[2]>1:dr.line((ground,feet),fill=AMBER,width=1)
    goomba(dr,feet,row)
    mp=mini(row[1:4]);dr.ellipse((mp[0]-4,mp[1]-4,mp[0]+4,mp[1]+4),fill=AMBER)
    action='Jumping' if row[5]==2 else 'Walking'
    title='Closest recorded point — rim not reached' if hold and args.direct_rim else 'Waypoint pause — still outside the rim' if hold else f'{action}   |   update {row[0]:03d} / {len(ROWS)}   |   {row[0]/30:.2f} s'
    dr.text((32,666),title,font=F24,fill=AMBER if not hold else BLUE)
    dr.text((32,704),f'(X, Y, Z) = ({row[1]:.2f}, {row[2]:.2f}, {row[3]:.2f})',font=F20,fill=FG)
    if args.home_range:
        dist=DATA['home']['distances'][index]
        dr.text((884,666),f'Home distance: {dist:.1f}',font=F20,fill=MINT)
        dr.text((884,704),'Beyond threshold' if dist>1000 else 'Within threshold',font=F20,fill=MINT)
    else:
        dr.line((670,716,1248,716),fill='#304553',width=5)
        dr.line((670,716,670+578*row[0]/len(ROWS),716),fill=AMBER,width=5)
    return im

def home_overview():
    """Equal-scale overhead view; not a geometric reachability certificate."""
    im=Image.new('RGB',(1280,850),BG);dr=ImageDraw.Draw(im)
    dr.text((32,23),'The rim target is inside the Goomba\'s home range',font=F30,fill=FG)
    dr.text((32,66),'Overhead view • same recorded path • all positions shown in game X/Z coordinates',font=F20,fill=MUTED)
    center=(387,431);scale=.285;home=DATA['home']['center']
    def p(v): return (center[0]+(v[0]-home[0])*scale,center[1]+(v[2]-home[2])*scale)
    layer=Image.new('RGBA',im.size,(0,0,0,0));ld=ImageDraw.Draw(layer)
    for face in sorted(DATA['mesh']['faces'],key=lambda f:sum(v[1] for v in f['vertices'])):
        if normal(face['vertices'])[1]<=0 or max(v[1] for v in face['vertices'])>180:continue
        poly=face['vertices']
        for axis,low,high in ((0,-4738,-2538),(2,828,3028)):
            poly=clipped(poly,axis,low,True)
            if poly:poly=clipped(poly,axis,high,False)
            if not poly:break
        if len(poly)>2:
            color=(124,106,69,100) if sum(v[1] for v in poly)/len(poly)<-20 else (119,145,143,65)
            ld.polygon([p(v) for v in poly],fill=color)
    im=Image.alpha_composite(im.convert('RGBA'),layer).convert('RGB');dr=ImageDraw.Draw(im)
    # The circle is the Y=0 cross-section of the actual three-dimensional test.
    dashed(dr,home_circle(p),MINT,3)
    x,y=center;dr.line((x,y,x+1000*scale,y),fill=MINT,width=1)
    label(dr,(x+175,y-23),'1,000',MINT)
    start=p(home);end=p(DATA['originalRimTarget']);way=p(DATA['waypoint']['position'])
    points=[p([r[1],0,r[3]]) for r in ROWS]
    dr.line(points,fill=AMBER,width=3)
    dashed(dr,[(x+(end[0]-x)*i/100,y) for i in range(101)],FG,3,10)
    # Actual highlighted collision faces project to this same vertical edge.
    for face in DATA['mesh']['faces']:
        if face['ordinal'] in (336,337):
            a,b,c=map(p,face['vertices']);dr.line((a,b,c,a),fill=RED,width=4)
    ring(dr,start,7,AMBER);star(dr,end,10,RED);ring(dr,way,8,BLUE)
    label(dr,(start[0]-8,start[1]-43),'Home / start',AMBER,anchor='rt')
    label(dr,(start[0]-8,start[1]-17),'(-3638, 0, 1928)',AMBER,anchor='rt')
    dr.line((end[0],end[1],702,369),fill=RED,width=1)
    label(dr,(706,336),'Original rim target',RED)
    label(dr,(706,363),'567 horizontally; 578 including Y',RED)
    dr.line((way[0],way[1],707,637),fill=BLUE,width=1)
    label(dr,(713,615),'Replay waypoint (update 847)',BLUE)
    label(dr,(713,642),'1,063 units from home',BLUE)
    label(dr,(713,673),'Outside the rim; beyond home threshold',BLUE)
    dr.text((744,145),'Why the curve?',font=F24,fill=FG)
    for j,t in enumerate(['The replay aimed near the wall\'s','southern end, at X=-3200, Z=2925.','It is one available RNG sequence,','not a shortest path to the rim.']):
        dr.text((744,183+27*j),t,font=F20,fill=MUTED)
    dr.text((744,419),'The direct obstacle is the wall.',font=F24,fill=FG)
    for j,t in enumerate(['The original target is well inside','the 1,000-unit home threshold.','Crossing the entry wall failed in','the isolated movement check.']):
        dr.text((744,458+27*j),t,font=F20,fill=MUTED)
    dr.text((74,747),'N / -Z ↑       +X →',font=F18,fill=MUTED)
    dr.text((32,795),'Mint: home threshold at Y=0    Amber: recorded path    White: direct bearing    Red: wall and target',font=F18,fill=FG)
    dr.text((32,824),'The home test uses all three coordinates. It steers behavior; it does not clamp position to the circle.',font=F18,fill=MUTED)
    return im

OUT.mkdir(parents=True,exist_ok=True)
if args.home_range and not args.direct_rim:home_overview().save(OUT/'western-goomba-home-range.png')
if args.preview:
    for i in sorted({0,len(ROWS)//3,len(ROWS)*2//3,PAUSE,len(ROWS)-1}):frame(i,i==PAUSE).save(OUT/f'preview-{i+1}.png')
else:
    frames=OUT/'frames';frames.mkdir(exist_ok=True)
    # Every source row appears once at 30 updates/s, with a three-second pause.
    sequence=[(i,False) for i in range(PAUSE+1)]+[(PAUSE,True)]*90+[(i,False) for i in range(PAUSE+1,len(ROWS))]+[(len(ROWS)-1,False)]*60
    for out_index,(row,hold) in enumerate(sequence):
        frame(row,hold).save(frames/f'{out_index:04d}.png',compress_level=1)
        if out_index%150==0:print(f'Rendered {out_index}/{len(sequence)}',flush=True)
    (OUT/'render-receipt.json').write_text(json.dumps({'frames':len(sequence),'fps':30,'traceRows':len(ROWS),'waypointPauseFrames':90,'finalHoldFrames':60,'csvSha256':DATA['csvSha256'],'dimensions':[W,H],'homeRangeOverlay':args.home_range},indent=2))
    print(f'Frames: {frames}',flush=True)
