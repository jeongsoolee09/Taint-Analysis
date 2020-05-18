# SpecHunter의 정적 분석 모듈

SpecHunter의 정적 분석 모듈은 infer의 Fix-Point Engine을 기반으로 합니다. defLocAlias.ml (변수의 definition과 그 definition의 location, 그리고 그 변수의 alias set을 트래킹한다는 뜻에서)이 정적 분석을 실제로 수행하는 핵심 코드 중 하나이고, defLocAlias.ml은 infer의 checker로 구현되어 있습니다. 그리고 checker 폴더에 들어 있는 defLocAliasSearches.ml과 defLocAliasLogicTests, 그리고 defLocAliasDomain.ml은 모두 위에서 언급한 defLocAlias.ml가 참조하는 함수, 변수 또는 모듈 정의를 담고 있습니다.

## defLocAlias.ml


### module Payload

Interprocedural analysis에서 summary가 무엇인지를 정의하는 모듈입니다. 여기서 하나의 summary는 abstract state들, 즉 튜플들의 집합입니다. Callee의 CFG 상에서 Exit 노드까지 축적된 최종적인 튜플들의 집합을 그대로 가져다 사용합니다.

### module TransferFunctions

Abstract Semantic을 정의하는 핵심적인 모듈입니다. 이전 Program Point에서의 Set of abstract states에서 다음 Program Point에서의 Set of abstract states로의 이행이 어떻게 일어나는지는 `exec_instr` 함수에서 정의하고 있습니다. 나머지는 `exec_instr` 함수가 참조하는 정의들입니다.


