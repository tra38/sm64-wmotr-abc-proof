"""Source-derived stills: recorded paths, stock heights and elevator timing.
Uses Pillow. This draws saved evidence and never moves an actor in a game.
"""
import json
import math
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'build/instrumentation/western-goomba-rng/elevator-analysis'
DATA=json.loads((OUT/'report.json').read_text())
MESH=json.loads((ROOT/'build/instrumentation/western-goomba-rng/video/data.json').read_text())['mesh']
BG,FG,MUTED='#101c26','#edf2f2','#abbcc7'
AMBER,BLUE,MINT,RED='#ffcc68','#75bfce','#8ed7ba','#ee7766'
FONT=Path('C:/Windows/Fonts/segoeui.ttf')
if not FONT.exists():FONT=Path('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf')
F18,F20,F24,F30=[ImageFont.truetype(str(FONT),n) for n in (18,20,24,30)]


def label(d,xy,text,fill=FG,font=F18,anchor=None):
    d.text(xy,text,font=font,fill=fill,anchor=anchor,stroke_width=2,stroke_fill=BG)


def circle(d,p,text,filled=True):
    x,y=p
    d.ellipse((x-12,y-12,x+12,y+12),fill=AMBER if filled else BG,outline=AMBER if filled else MUTED,width=2)
    d.text((x,y-1),str(text),font=F18,anchor='mm',fill=BG if filled else MUTED)


def normal_y(v):
    a,b,c=v
    return (b[2]-a[2])*(c[0]-a[0])-(b[0]-a[0])*(c[2]-a[2])


def map_image():
    im=Image.new('RGB',(1280,960),BG);d=ImageDraw.Draw(im)
    d.text((32,20),'Six Goomba paths tested; three children need a spawner',font=F30,fill=FG)
    d.text((32,66),'Overhead view • exact recorded positions • elevator footprint stays fixed in X/Z',font=F20,fill=MUTED)
    scale=.074;cx,cy=381,459
    def p(x,z):return cx+x*scale,cy+z*scale
    # Low static geometry only; the upper floors would conceal these paths.
    for f in sorted(MESH['faces'],key=lambda x:sum(v[1] for v in x['vertices'])):
        if normal_y(f['vertices'])<=0 or max(v[1] for v in f['vertices'])>800:continue
        d.polygon([p(v[0],v[2]) for v in f['vertices']],fill='#374544' if sum(v[1] for v in f['vertices'])>=0 else '#4d4736')
    a,b=p(-511,-255),p(512,768)
    d.rectangle((a,b),fill='#2d656b',outline=BLUE,width=2)
    label(d,(a[0]-5,a[1]-24),'Elevator base',BLUE)
    pole=p(0,1331);d.line((pole[0]-7,pole[1],pole[0]+7,pole[1]),fill=RED,width=2)
    d.line((pole[0],pole[1]-7,pole[0],pole[1]+7),fill=RED,width=2)
    label(d,(pole[0]-11,pole[1]+10),'Second pole',RED,anchor='rt')
    for actor in DATA['actors']:
        x,z=actor['x'],actor['z']
        points=[p(x+1000*math.cos(i*math.tau/120),z+1000*math.sin(i*math.tau/120)) for i in range(121)]
        for i in range(120):
            if i%6<3:d.line((points[i],points[i+1]),fill='#597167',width=1)
        if actor['search']:
            states=actor['search']['states']
            d.line([p(r['x'],r['z']) for r in states],fill=AMBER,width=2)
            best=actor['search']['best'];q=p(best['x'],best['z'])
            d.ellipse((q[0]-4,q[1]-4,q[0]+4,q[1]+4),outline=FG,width=2)
        circle(d,p(x,z),int(actor['id'])+1,actor['search'] is not None)
    label(d,(40,822),'N / -Z ↑    +X →',MUTED)
    d.line((758,120,758,843),fill='#304553')
    d.text((794,122),'Actor / starting floor / tested result',font=F20,fill=FG)
    descriptions={0:'Leaves raised ledge for the pit',1:'Remains outside the pit rim',2:'Remains outside the pit rim',
                  3:'Reaches low ground in the pit',4:'Reaches low ground in the pit',5:'Remains outside the pit rim'}
    for i,actor in enumerate(DATA['actors']):
        y=177+i*69
        circle(d,(805,y+10),i+1,actor['search'] is not None)
        d.text((827,y-5),f"{actor['name']}  ·  Y={actor['homeY']:.0f}".replace('Y=-0','Y=0'),font=F20,fill=FG)
        d.text((827,y+22),descriptions[i] if i<6 else 'Cannot first spawn from the bucket',font=F18,fill=MUTED)
    d.text((32,876),'Amber lines: selected RNG-choice replays. Hollow white dots: their closest approach to the chosen base target.',font=F18,fill=FG)
    d.text((32,904),'Dashed circles: 1,000-unit home threshold at each home height; steering thresholds, not hard movement limits.',font=F18,fill=MUTED)
    d.text((32,930),'Static terrain and one actor per test. Other actors and moving collision surfaces are absent. No shortest-path proof.',font=F18,fill=MUTED)
    return im


def height_image():
    im=Image.new('RGB',(1280,800),BG);d=ImageDraw.Draw(im)
    d.text((32,20),'All stock Goombas are far below the second pole',font=F30,fill=FG)
    d.text((32,65),'Elevator floor height after it detects Mario standing on it • 30 game updates per second',font=F20,fill=MUTED)
    left,right,top,bottom=106,876,131,670
    def p(t,y):return left+(right-left)*t/18,bottom-(bottom-top)*y/5200
    for y in (0,1000,2000,3000,4000,5000):
        a,b=p(0,y),p(18,y);d.line((a,b),fill='#263b48')
        d.text((left-14,a[1]),str(y),font=F18,fill=MUTED,anchor='rm')
    for t in (0,3,6,9,12,15,18):
        a,b=p(t,0),p(t,5200);d.line((a,b),fill='#263b48')
        d.text((a[0],bottom+17),str(t),font=F18,fill=MUTED,anchor='mt')
    d.line([p(r['seconds'],r['elevator_y']) for r in DATA['elevator'] if r['seconds']<=18],fill=BLUE,width=4)
    for y,color in ((4020,RED),(640,AMBER),(0,AMBER)):
        a,b=p(0,y),p(18,y);d.line((a,b),fill=color,width=2)
    label(d,(p(.15,4020)[0],p(.15,4020)[1]-29),'Mario at upper grip: Y=4020',RED)
    label(d,(p(.15,640)[0],p(.15,640)[1]-28),'Three raised singletons: floor Y=640',AMBER)
    label(d,(p(.15,0)[0],p(.15,0)[1]-28),'Three low singletons + three potential children: Y=0',AMBER)
    milestones=[(104/30,4016,'3.47 s',(34,19)),(442/30,636,'14.73 s',(-15,-58)),(493/30,128,'16.43 s',(7,-59))]
    for t,y,text,offset in milestones:
        x,sy=p(t,y);d.ellipse((x-5,sy-5,x+5,sy+5),fill=FG)
        d.line((x,sy,x+offset[0],sy+offset[1]),fill=MUTED)
        label(d,(x+offset[0],sy+offset[1]),text,font=F20)
    label(d,(p(.1,4966)[0]+10,p(.1,4966)[1]-25),'Start Y=4966',BLUE)
    d.text((925,164),'Passing a height',font=F24,fill=FG)
    for j,t in enumerate(['is not reaching a Goomba.','Their starting X/Z positions','are 3,003–4,241 units from','the elevator’s full footprint.']):
        d.text((925,202+29*j),t,font=F18,fill=MUTED)
    d.text((925,386),'What the clock shows',font=F24,fill=FG)
    for j,t in enumerate(['Upper grip passed: 3.47 s','Raised floor passed: 14.73 s','Bottom first reached: 16.43 s','Bottom jolt ends: 16.73 s','Low floor Y=0: never reached']):
        d.text((925,427+32*j),t,font=F18,fill=MUTED)
    d.text((453,722),'Seconds after the trigger update',font=F20,fill=FG,anchor='mt')
    d.text((32,762),'Source-loop timing with normal timer updates. Height comparison alone supplies no contact, escape or pole bypass.',font=F18,fill=MUTED)
    return im


map_image().save(OUT/'goomba-elevator-map.png')
height_image().save(OUT/'goomba-elevator-height.png')
print(OUT)
