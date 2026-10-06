from common import *
from PIL import Image
full=Path(load(RUN/'formula-render-v3.json')['snapshot']);dest=RUN/'formula-render-v3-full.png';write(dest,full.read_bytes());assert sha(dest)==sha(full)
crop=RUN/'formula-render-v3-source-card.png';box=(0,4300,1440,5650)
with Image.open(full) as im:im.crop(box).save(str(crop))
write(RUN/'formula-source-crop-binding-v3.json',dict(source=full.as_posix(),source_sha256=sha(full),exact_full_copy=dest.as_posix(),exact_full_copy_sha256=sha(dest),crop=crop.as_posix(),crop_sha256=sha(crop),crop_box_in_original_pixels=box,change='Inspection crop of actual screenshot only; generated site/HTML/TeX unmodified.',visual_review_pending=True))
