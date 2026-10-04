"""Version 3 compact chunks; old v2 chunks are read without rewriting them."""
from chunk_ledger import ChunkLedger, STATUSES


class ProductCodec:
    name = 'product-recipes-gzip-v1'

    def __init__(self, signature):
        self.signature = signature

    def encode(self, record):
        return [record['case'], record['jobId'], record['inputIndex'],
                STATUSES.index(record['status']), record['detail']]

    def decode(self, row):
        from product_sweep import decode_input
        if (not isinstance(row,list) or len(row)!=5
                or any(type(x) is not int for x in row[:4])
                or not 0<=row[1]<len(self.signature['jobOrder']) or not 0<=row[3]<len(STATUSES)):
            raise ValueError('Invalid compact trial')
        case, job, index, status, detail = row
        recipe = self.signature['jobOrder'][job]
        control = decode_input(index,self.signature['aMode'],self.signature['inputSpace']['buttonsMode'])
        return dict(case=case,jobId=job,inputIndex=index,status=STATUSES[status],detail=detail,
                    setup=recipe['setup'],pose=recipe['move'],input=control.record())


def open_product(root, manifest, **options):
    from product_sweep import validate_record
    codec = ProductCodec(manifest['signature']) if manifest['schema']==3 else None
    if manifest['schema'] not in (2,3) or (codec and manifest['storage']!=codec.name):
        raise ValueError('Unsupported ledger storage format')
    return ChunkLedger(root,manifest['signature'],manifest['totalCases'],
                       validate_record(manifest['signature']),resume=True,
                       chunk_records=manifest['chunkRecords'],codec=codec,**options)
