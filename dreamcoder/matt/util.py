import hydra
from hydra.utils import to_absolute_path
from omegaconf import DictConfig,OmegaConf,open_dict
from datetime import datetime
import os
import pathlib

def ec_path(p):
    return pathlib.Path(to_absolute_path(p))
def outputs_path(p):
    return ec_path('outputs') / p
def toplevel_path(p):
    return outputs_path('_toplevel') / p
def printable_local_path(p):
    """
    In:  plots/x.png
    Out: 12-31-20/12-23-23/plots/x.png
    """
    return hide_path_prefix(pathlib.Path(os.getcwd())) / p
def yaml(cfg):
    return OmegaConf.to_yaml(cfg)
def timestamp():
    return datetime.now()
def which(cfg=None):
    print(yaml(cfg))
    print(os.getcwd())
    regex = os.path.basename(os.path.dirname(os.getcwd())) + '%2F' + os.path.basename(os.getcwd())
    print(f'http://localhost:6696/#scalars&regexInput={regex}')
    print("curr time:",timestamp())

def outputs_regex(*rs, sort=True):
    """
    The union of one or more regexes over the outputs/ directory.
    Returns a list of results (pathlib.Path objects)
    """
    res = []
    for r in rs:
        r = r.strip()
        if r == '':
            continue # use "*" instead for this case please. I want to filter out '' bc its easy to accidentally include it in a generated list of regexes
        try:
            r = f'**/*{r}'
            res.extend(list(outputs_path('').glob(r)))
        except ValueError as e:
            print(e)
            return []
    if sort:
        return sorted(res)
    return res

def hide_path_prefix(p):
    """
    remove everything in path before the `outputs` dir (inclusive) eg:
    In:  /scratch/mlbowers/proj/ec/outputs/2020-09-17/15-22-30
    Out: 2020-09-17/15-22-30
    """
    idx = p.parts.index('outputs')+1 # points to DATE dir
    return pathlib.Path(*p.parts[idx:])

def get_datetime_path(p):
    """
    Path -> Path
    In:  .../2020-09-14/23-31-49/t3_reverse.no_ablations_first
    Out: .../2020-09-14/23-31-49
    Harmless on shorter paths
    """
    idx = p.parts.index('outputs')+3 # points one beyond TIME dir
    return pathlib.Path(*p.parts[:idx]) # only .../DATE/TIME dir
def get_datetime_paths(paths):
    return [get_datetime_path(p) for p in paths]

def filter_paths(paths, predicate):
    return [p for p in paths if predicate(p)]

    # then filter using predicates
    for predicate in [arg for arg in args if '=' in arg]:
        lhs,rhs = predicate.split('=')
        # TODO WAIT FIRST JUST FOLLOW THIS https://github.com/tensorflow/tensorboard/issues/785
        # idk it might be better.
        # TODO first navigate to the actual folder that the tb files are in bc thats 
        # what process() should take as input (e.g. 'tb' or whatever prefix+name is)
        process(result)
        raise NotImplementedError

    return results




class Saveable:
  """
  Things you can do:
    * define a class variable no_save = ('hey','there') if you want self.hey and self.there to not be pickled
    * define a method `post_load(self) -> None` which will be called by setstate after unpickling. Feel free to call it yourself in __init as well if you want it during __init too.
  Extras:
    * a repr() implementation is written for you
    * __getitem and __setitem are defined for you so you can do self.k instead of self.__dict__['k']. Note that it errors if you try to overwrite an @property
    * .update(dict) is defined for you and does bulk setattr

  """
  no_save = ()
  def __getstate__(self):
    return {k:v for k,v in self.__dict__.items() if k not in self.no_save}
  def __setstate__(self,state):
    self.__dict__.update(state)
    self.post_load()
  def post_load(self):
	  pass
  def __getitem__(self,key):
      return getattr(self,key)
  def __setitem__(self,key,val):
    if hasattr(self,key) and isinstance(getattr(type(self),key), property):
      raise ValueError
    return setattr(self,key,val)
  def __repr__(self):
      body = []
      for k,v in self.__dict__.items():
          body.append(f'{k}: {repr(v)}')
      body = '\n\t'.join(body)
      return f"{self.__class__.__name__}(\n\t{body}\n)"
  def update(self,dict):
      for k,v in dict.items():
          if hasattr(type(self), k) and isinstance(getattr(type(self),k), property):
              continue # dont overwrite properties (throws error)
          self[k] = v
