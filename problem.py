from pathlib import Path
from typing import Any, Dict, List, NamedTuple

class Problems:
    def __init__(self, relative_path:Path, general_options:Dict[str, Any], defaults:Dict[str, Any]):
        self._relative_path = relative_path
        self._general_options = general_options
        self._defaults = defaults
        self._problems = []

    def add_problem(self, problem:NamedTuple):
        self._problems.append(problem)

    @property
    def problems(self)->List[NamedTuple]:
        return self._problems
