'''
如果 不想依赖pydantic可以通过dataclasses实现。但是dataclasses还部支持 json序列化,未来路可能不好走
'''
from pydantic import BaseModel,Field


class ChromiumWebContent:
    id:str=Field(pattern='[0-9A-F]{32}')
    
