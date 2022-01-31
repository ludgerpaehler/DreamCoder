from dreamcoder.domains.list.listPrimitives import bootstrapTarget_extra
from dreamcoder.grammar import DataAwareGrammar, Grammar
from dreamcoder.program import Program
from dreamcoder.task import NamedVarsTask, Task
from dreamcoder.type import tlist, tint, arrow


def test_data_aware_grammar():
    prims = bootstrapTarget_extra()
    baseGrammar = Grammar.uniform(prims)
    baseGrammar = DataAwareGrammar(
        baseGrammar,
        {
            "list": 1.0,
            "int": 1.0,
            "bool": 1.0,
            "float": 1.0,
        },
    )
    task = NamedVarsTask(
        Task(
            name="drop-k with k=1",
            request=arrow(tlist(tint), tlist(tint)),
            examples=[
                (([15, 1],), [1]),
                (([15, 8, 10, 1, 14, 1, 3],), [8, 10, 1, 14, 1, 3]),
                (([6, 8, 8, 1, 9],), [8, 8, 1, 9]),
                (([11, 2, 10, 10],), [2, 10, 10]),
                (([13, 2],), [2]),
                (([4, 7, 11, 4, 2, 5, 13, 5],), [7, 11, 4, 2, 5, 13, 5]),
                (([12, 0],), [0]),
                (([0, 1, 2, 7, 16, 3],), [1, 2, 7, 16, 3]),
                (([16, 2, 1, 12, 1, 11, 15],), [2, 1, 12, 1, 11, 15]),
                (([9, 9, 15],), [9, 15]),
                (([6, 4, 15, 0],), [4, 15, 0]),
                (([5, 16, 16, 9],), [16, 16, 9]),
                (([8],), []),
                (([16],), []),
                (([3, 13],), [13]),
            ],
        )
    )
    programs = [
        (
            "(cdr $inp0)",
            {
                "inp0": {
                    "list": 15,
                    "int": 58,
                },
                "out": {
                    "list": 15,
                    "int": 43,
                },
            },
            -2.302585092994046,
        ),
        (
            "let $v1 = (eq? $inp0 $inp0) in let $v2 = (cdr $inp0) in (if $v1 $v2 empty)",
            {
                "inp0": {
                    "list": 15,
                    "int": 58,
                },
                "out": {
                    "list": 15,
                    "int": 43,
                },
                "v1": {
                    "bool": 15,
                },
                "v2": {
                    "list": 15,
                    "int": 43,
                },
            },
            -10.021270588192511,
        ),
        (
            "let $v1 = (eq? $inp0 $inp0) in let $v2, $v3 = rev((cons FREE_VAR FREE_VAR), [$inp0]) in (if $v1 $v3 empty)",
            {
                "inp0": {
                    "list": 15,
                    "int": 58,
                },
                "out": {
                    "list": 15,
                    "int": 43,
                },
                "v1": {
                    "bool": 15,
                },
                "v2": {
                    "int": 15,
                },
                "v3": {
                    "list": 15,
                    "int": 43,
                },
            },
            -8.006367567650248,
        ),
        (
            "let $v1, $v2 = rev((cons FREE_VAR FREE_VAR), [$inp0]) in $v2",
            {
                "inp0": {
                    "list": 15,
                    "int": 58,
                },
                "out": {
                    "list": 15,
                    "int": 43,
                },
                "v1": {
                    "int": 15,
                },
                "v2": {
                    "list": 15,
                    "int": 43,
                },
            },
            -0.6931471805599453,
        ),
    ]
    for program, complexities, expected_likelihood in programs:
        p = Program.parse(program)
        print(p)
        likelihood = baseGrammar.logLikelihood(task, p, complexities)
        print(likelihood)
        # assert likelihood == expected_likelihood
