# SpecHunter: Interactively Inferring Taint Specifications Using Bayes Net

Repository 책임자: 이정수

## Directory Description

### Reading-List

기존 연구 논문이 들어 있는 폴더와 논문의 카탈로그 파일이 들어 있는 폴더입니다.

### Code

구현체가 들어 있는 폴더입니다.

### My-Paper

본 연구에 관한 논문 파일이 들어 있습니다.

## Installation Guide

우선, 해당 repository를 clone합니다.

### Dependency

1. Java 11 (Oracle)
2. 최신 Gradle
3. 최신 opam과 OCaml 4.08.1
4. Python 3.8.5
5. `pip install numpy matplotlib networkx toolz pandas pomegranate ray dask modin[all] bs4` 

### Infer 설치하기

SpecHunter는 정적분석 모듈로 Facebook에서 개발한 오픈 소스 정적 분석 프레임워크를 사용합니다.

infer directory로 이동합니다:

```shell
$ cd Code/infer
```

다음을 실행합니다:

```shell
$ ./build-infer.sh java && sudo make install && cd infer/src && make -k
```

### 제공된 벤치마크에 대해 SpecHunter 실행하기

Repository의 루트로 돌아가서 다음을 실행합니다:

```shell
$ cd Code/benchmarks/realworld
```

여기에는 Spring Boot로 만들어진 간단한 (100LoC) 애플리케이션인 relational-data-access와 spring.io 웹사이트를 구동하는 sagan이라는 애플케이션이 있습니다. 여기서는 relational-data-access를 예를 들어 설명해 보겠습니다.

해당 디렉토리로 이동합니다:

```shell
$ cd relational-data-access
```

그 다음, 이 디렉토리에서 infer를 실행합니다:

```shell
$ infer -g run -- gradle build
$ infer spechunter
```

디렉토리에 다음의 파일/디렉토리가 생겼다면 성공입니다:

- Callgraph.txt
- Chain.json
- Methods.txt
- infer-out/
- skip_func.txt

그 다음, Repository의 루트로 돌아가서 다음을 실행합니다:

```shell
$ cd Code/BayesianNetwork
```

`paths.json`을 열어 다음과 같이 수정합니다:

```json
{
    "project_root_directory":"../benchmarks/realworld/relational-data-access/",
    "solution_directory":"solution_relational.json"
}
```

다음을 실행합니다:

```shell
$ python create_node.py
$ python create_edge.py
$ python make_underlying_graph.py
$ python split_underlying_graph.py
```

이제 loop을 실행할 수 있는 준비가 모두 끝난 것입니다.

#### loop.py 사용하기

매 interaction마다 직접 레이블을 입력하는 loop을 원한다면, 다음을 실행합니다:

```shell
$ python loop.py
```

매 interaction마다 총 4개의 matplotlib figure가 보여지고, 업데이트됩니다:

1. Bayesian Network: 가시화된 Bayesian Network입니다.
2. Precision: Bayesian Network가 맞힌 노드 레이블의 개수입니다.
3. Stability: 이전 Bayesian Network의 snapshot에 비해 현재 Bayesian Network의 snapshot에서 몇 개의 노드의 레이블이 변화되었는지를 나타냅니다.
4. Inferred Precision: 외부에서 주어진 정답 외에, Bayesian Network가 순수하게 추론해서 맞힌 노드들의 개수입니다.

`loop.py`가 끝나면, inference가 진행된 그래프에 대한 statistics가 생성됩니다. 예를 들어, `sagan-site_graph_0`에 대해 `loop.py`를 실행하셨다면 (`loop.py`의 `GRAPH_FILE_NAME`으로 확인할 수 있습니다), `sagan-site_graph_0_stats`라는 디렉토리 하에 관련 그래프가 기록됩니다.

##### Bayesian Network 바꾸기 (Sagan에만 해당)

위에서 실행한 `split_underlying_graph.py`는 Bayesian Network를 `.jar`로 컴파일되는 단위로 쪼개고, 그렇게 쪼갰을 때 나오는 그래프의 노드 개수가 200개 미만이 될 때까지 recursive하게 그래프를 이등분합니다. 따라서, 현재 `Code/BayesianNetwork` 하에는 여러 개의 그래프들이 들어 있을 겁니다:

- `sagan-renderer_graph`
- `sagan-renderer_graph_0`
- `sagan-site_graph`
- `sagan-site_graph_0`
- `sagan-site_graph_1`
- `sagan-site_graph_2`
- `sagan-site_graph_3`
- `sagan-site_graph_4`
- `sagan-site_graph_5`
- `sagan-site_graph_6`

이 중에서, 뒤에 *숫자가 붙은 그래프만을 사용할 겁니다.*

`loop.py`를 열어 `GRAPH_FILE_NAME` 변수를 다른 그래프 이름으로 바꾸어 줍니다. 예를 들어, 다음으로 `sagan-site_graph_1`을 실행하고자 한다면 변수명을 다음과 같이 바꿉니다:

```python
GRAPH_FILE_NAME = "sagan-site_graph_1"
```

이후 다시 `python loop.py`를 통해 해당 그래프에 대한 interactive inference를 진행합니다.

#### self-question-and-answer 사용하기

Oracle이 직접 알려줄 필요 없이, 매 interaction마다 정답 파일 (`solution-relational.json` 등)에서 매 interaction마다 직접 답을 가져오게 하려면 다음을 실행합니다:

```shell
$ python self-question-and-answer.py
```

한번 loop을 돌 때마다 다음이 표시됩니다:

1. 해당 interaction에서의 정답률
2. 해당 interaction에 걸린 시간

`self-question-and-answer.py`가 끝나면, inference가 진행된 그래프에 대한 statistics가 생성됩니다. 예를 들어, `sagan-site_graph_0`에 대해 `loop.py`를 실행하셨다면 (`loop.py`의 `GRAPH_FILE_NAME`으로 확인할 수 있습니다), `sagan-site_graph_0_stats`라는 디렉토리 하에 관련 그래프가 기록됩니다.

##### Bayesian Network 바꾸기 (Sagan에만 해당)

위에서 실행한 `split_underlying_graph.py`는 Bayesian Network를 `.jar`로 컴파일되는 단위로 쪼개고, 그렇게 쪼갰을 때 나오는 그래프의 노드 개수가 200개 미만이 될 때까지 recursive하게 그래프를 이등분합니다. 따라서, 현재 `Code/BayesianNetwork` 하에는 여러 개의 그래프들이 들어 있을 겁니다:

- `sagan-renderer_graph`
- `sagan-renderer_graph_0`
- `sagan-site_graph`
- `sagan-site_graph_0`
- `sagan-site_graph_1`
- `sagan-site_graph_2`
- `sagan-site_graph_3`
- `sagan-site_graph_4`
- `sagan-site_graph_5`
- `sagan-site_graph_6`

이 중에서, 뒤에 *숫자가 붙은 그래프만을 사용할 겁니다.*

`loop.py`를 열어 `GRAPH_FILE_NAME` 변수를 다른 그래프 이름으로 바꾸어 줍니다. 예를 들어, 다음으로 `sagan-site_graph_1`을 실행하고자 한다면 변수명을 다음과 같이 바꿉니다:

```python
GRAPH_FILE_NAME = "sagan-site_graph_1"
```

이후 다시 `python loop.py`를 통해 해당 그래프에 대한 inference를 진행합니다.

### 다른 벤치마크에 대해 SpecHunter 사용하기

SpecHunter를 기본으로 제공되어 있지 않은 다른 벤치마크에 대해 사용하는 것은 기본으로 제공되는 벤치마크에 대해 사용하는 것과 크게 다르지 않습니다.

#### infer 실행하기

사용하고자 하는 프로젝트의 root directory로 이동해 다음을 실행합니다 (프로젝트에 들어 있는 `.java` 파일 개수에 따라 시간이 오래 걸릴 수도 있습니다, 여러 개의 코어가 있는 서버급 워크스테이션에서 실행하시는 것을 권장드립니다):

```shell
$ infer -g run -- gradle build
$ infer spechunter
```

그 다음, Repository의 루트로 돌아가서 다음을 실행합니다:

```shell
$ cd Code/BayesianNetwork
```

`paths.json`을 열어 다음과 같이 수정합니다:

```json
{
    "project_root_directory":"<프로젝트 루트 디렉토리>",
    "solution_directory":"solution_relational.json"
}
```

`"solution_directory"`에 대한 값은 그대로 둡니다. (어차피 사용하지 않을 겁니다.)

다음을 실행합니다:

```shell
$ python create_node.py
$ python create_edge.py
$ python make_underlying_graph.py
$ python split_underlying_graph.py
```

#### loop.py 사용하기

여기서 `self-question-and-answer.py`는 사용하지 못합니다: 이를 사용하기 위해서는 SpecHunter를 사용하고자 하는 대상 프로젝트의 모든 메소드에 대한 레이블 (source, sink, sanitizer, none)이 모두 ground truth로서 주어져 있어야 하기 때문입니다. 따라서, loop.py를 사용할 것입니다.

**중요**: `loop.py`의 644번째 줄의 코드 중 `have_solution`의 값을 `False`로 수정합니다: 수정하고 나면 다음과 같아야 합니다.

```python
    # tactical loop
    print("\nEntering tactical loop.\nPress 'exit' on the prompt to exit the loop.\n")
    final_snapshot, precision_list, stability_list, precision_inferred_list=\
        tactical_loop(graph_for_reference, 0,
                      list(), dict(), list(),
                      initial_snapshot, initial_precision_list, initial_stability_list,
                      initial_precision_inferred_list, list(), have_solution=False)
```

이제 그래프들이 출력되지 않고, 대신 `# of confident nodes`가 stdout에 출력될 것입니다. 이는 "확실하게" 업데이트가 된 노드들의 개수로, source/sink/sanitizer/none 넷 중 하나일 믿음(확률)이 다른 셋에 비해 적어도 0.1보다 높다는 뜻입니다.

인터렉션 중 `exit`을 눌러 loop에서 빠져나올 수 있습니다. 참고로, 저희 실험상 35-40번째 interaction에서 70%의 정답률을 기록했습니다 (sagan 기준).

## Troubleshooting

### infer 명령어를 찾을 수 없는 경우

shell configuration file에 `infer` 명령어에 대한 alias를 다음으로 설정하시기 바랍니다:

```shell
<SpecHunter repository 루트 디렉토리>/Code/infer/infer/bin/infer
```

### pip install modin[all] 이 실패하는 경우

사용 중이신 shell이 zsh인 경우 발생하는 문제입니다. `pip install "modin[all]"`로 다시 시도해 보시기 바랍니다.

### infer 실행 시 Internal Error가 발생하는 경우

infer로 작성된 정적분석기가 다루지 못하는 케이스를 맞닥뜨린 경우입니다. 이는 현재 한계로 남아 있습니다.
