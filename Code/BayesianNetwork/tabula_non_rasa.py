# 백지 상태에서 시작하지 않고, 이전 경험에서부터 배우도록 하자.
import networkx as nx
import pandas as pd

from operator import itemgetter
from split_underlying_graph import draw_callgraph
from create_edge import no_symmetric
from create_node import process

# Constants ============================================
# ======================================================

SIM_VECTORS = pd.read_csv("sim_vectors.csv", index_col=0)
CALLGRAPH = nx.read_gpickle("callgraph")

# Functions ============================================
# ======================================================

def is_confident(parameters):
    """확률분포 (Distribution 오브젝트의 parameters 부분)를 보고, 가장 높은 확률이 다른 확률들보다 적어도 0.1은 높은지 확인한다."""
    if type(parameters) == dict:
        parameters = list(parameters.values())
    first_rank = max(parameters)
    parameters_ = parameters[:]
    parameters_.remove(first_rank)
    second_rank = max(parameters_)
    if first_rank - second_rank < 0.05:
        return False
    else:
        return True


def find_oracle_response(final_snapshot, current_asked):
    oracle_responses = []
    target_params = [{1.0: 1, 2.0: 0, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 1, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 1, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 0, 4.0: 1}]
    for state_name, param in final_snapshot:
        if param in target_params:
            label, _ = max(param.items(), key=itemgetter(1))
            oracle_responses.append((state_name, label))
    return oracle_responses


def find_conf_sols(final_snapshot, current_asked):
    conf_sols = []
    target_params = [{1.0: 1, 2.0: 0, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 1, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 1, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 0, 4.0: 1}]
    for state_name, param in final_snapshot:
        if param not in target_params and is_confident(param):
            label, _ = max(param.items(), key=itemgetter(1))
            conf_sols.append((state_name, label))
    return conf_sols

# A lesson is a dict from a node to label(1.0, 2.0, 3.0, 4.0).

def learn(previous_lessons, final_snapshot, current_asked):
    oracle_response = dict(find_oracle_response(final_snapshot, current_asked))
    conf_sols = dict(find_conf_sols(final_snapshot, current_asked))
    lessons = {**oracle_response, **conf_sols}
    return {**previous_lessons, **lessons}


sample_lesson = {'MemberProfile SignInService.getOrCreateMemberProfile(Long,GitHub)': 4.0,
                 'boolean Iterator.hasNext()': 4.0,
                 'String SaganRendererClient.renderMarkdown(String)': 2.0,
                 'void PostFormAdapter.updatePostFromPostForm(Post,PostForm)': 4.0,
                 'void TeamLocation.setName(String)': 4.0,
                 'List GuideContent.getImages()': 4.0,
                 'String ProjectAdminController.edit(String,Model)': 2.0,
                 'ProjectRepository ProjectRelease.getRepository()': 4.0,
                 'void DefaultTeamImporter.importTeamMembers(GitHub)': 2.0,
                 'void HttpHeaders.setAccept(List)': 4.0,
                 'GitHub GitHubConfig.gitHubTemplate()': 4.0,
                 'String PostCategoryFormatter.print(PostCategory,Locale)': 4.0,
                 'Post BlogService.addPost(PostForm,String)': 2.0,
                 'Optional Tutorials.findGuideHeaderByName(String)': 1.0,
                 'String SaganRendererClient.renderAsciidoc(String)': 2.0,
                 'GuideMetadata SaganRendererClient.fetchTutorialGuide(String)': 1.0,
                 'Post PostFormAdapter.createPostFromPostForm(PostForm,String)': 4.0,
                 'Set Collections.emptySet()': 4.0,
                 'Page PostView.pageOf(Page,DateFactory)': 4.0,
                 'org.springframework.social.github.api.GitHubUser[] DefaultTeamImporter.getGitHubUsers(GitHub)': 1.0,
                 'String ProjectAdminController.edit(Project,Model)': 1.0,
                 'Stream Collection.stream()': 4.0,
                 'void TeamLocation.setLatitude(float)': 4.0,
                 'void GeoLocation.setLongitude(float)': 4.0,
                 'String SpringToolsAdminController.edit(String,Model)': 1.0,
                 'String TeamAdminController.editTeamMemberForm(String,Model)': 2.0,
                 'void BlogService.updatePost(Post,PostForm)': 2.0,
                 'void PostFormAdapter.setPostProperties(PostForm,String,Post)': 4.0,
                 'void PostFormAdapter.summarize(Post)': 4.0,
                 'ProjectRelease ProjectMetadataController.releaseMetadata(String,String)': 4.0,
                 'ProjectRelease Project.removeProjectRelease(String)': 2.0,
                 'String SaganRendererClient.renderMarkup(String,MediaType)': 1.0,
                 'Object RestTemplate.postForObject(String,Object,Class,java.lang.Object[])': 2.0,
                 'Object RestOperations.postForObject(String,Object,Class,java.lang.Object[])': 1.0,
                 'void HttpHeaders.setContentType(MediaType)': 4.0,
                 'void Project.setDisplayOrder(int)': 4.0,
                 'Hop Hop.rel(String)': 4.0,
                 'String String.format(Locale,String,java.lang.Object[])': 4.0,
                 'Float Float.valueOf(float)': 4.0,
                 'AtomFeedView AtomFeedController.listPublishedPostsForCategory(PostCategory,Model,HttpServletResponse)': 1.0,
                 'String BlogController.listPublishedPostsForDate(int,int,int,int,Model)': 2.0,
                 'String Tutorial.getTypeLabel()': 4.0,
                 'UserOperations GitHub.userOperations()': 4.0,
                 'MemberProfile TeamService.createOrUpdateMemberProfile(Long,String,String,String)': 2.0,
                 'void AtomFeedView.setAuthor(Post,Entry)': 4.0,
                 'void AtomFeedView.setUpdatedDate(Map,Feed)': 4.0,
                 'List Tutorial.getImages()': 4.0,
                 'String BlogController.listPublishedBroadcasts(Model,int)': 2.0,
                 'AtomFeedView AtomFeedController.listPublishedPosts(Model,HttpServletResponse)': 1.0,
                 'String GeoLocationFormatter.print(GeoLocation,Locale)': 4.0,
                 'ProjectRelease ProjectMetadataController.removeReleaseMetadata(String,String)': 4.0,
                 'Optional BadgeController.getRelease(Collection,Predicate)': 4.0,
                 'Set Tutorial.getProjects()': 4.0,
                 'String BlogController.renderListOfPosts(Page,Model,String)': 4.0,
                 'String BlogController.listPublishedPostsForCategory(PostCategory,Model,int)': 2.0,
                 'List Collections.emptyList()': 4.0,
                 'String LearnController.learn(Model)': 4.0,
                 'String BlogController.listPublishedPosts(Model,int)': 2.0,
                 'void AtomFeedView.setCategories(Post,Entry)': 4.0,
                 'Optional Tutorials.findByName(String)': 1.0,
                 'void BlogService.resummarizeAllPosts()': 4.0,
                 'String PostCategoryFormatter.print(Object,Locale)': 4.0,
                 'GitHubConnectionFactory GitHubConfig.gitHubConnectionFactory()': 4.0,
                 'String ProjectRelease.getArtifactId()': 4.0,
                 'String GuideContent.getContent()': 4.0,
                 'boolean BindingResult.hasErrors()': 4.0}


def scoring_function(node1, node2):
    """cartesian product의 한 row를 받아서 두 node가 충분히 similar한지 판단하는 메소드"""
    ## node1의 feature vector를 retrieve
    node1_vector = SIM_VECTORS.loc[SIM_VECTORS['id'] == node1]
    node1_vector = node1_vector.drop(columns=['id'])

    ## node2의 feature vector를 retrieve
    node2_vector = SIM_VECTORS.loc[SIM_VECTORS['id'] == node2]
    node2_vector = node2_vector.drop(columns=['id'])
    
    node1_vector = node1_vector.astype(bool)
    node2_vector = node2_vector.astype(bool)

    elementwise_and = node1_vector & node2_vector

    true_count = elementwise_and.sum().sum()

    return True if true_count == 22 else False


def make_evidence(lessons, state_names):
    """lessons의 내용을 보고, state_names 중에서 충분히 닮은 것들, 그리고 1-call 관계에 있는 노드들을 찾아낸다."""

    ## 전처리: (class, rtntype, methodname, intype, id)의 튜플 리스트로 만들기
    lessons = list(lessons.keys())
    lessons = list(map(process, lessons))

    state_names = list(map(process, state_names))

    ## 두 개의 DF를 준비: 이전의 오라클 답변들과 현재 그래프의 노드 이름들
    previous_lessons_nodes = pd.DataFrame(lessons)  # 이전의 오라클 답변들
    state_names = pd.DataFrame(state_names)         # 다음에 갈아끼울 BN state 이름들

    previous_lessons_nodes.columns = ['class', 'rtntype', 'name', 'intype', 'id']
    state_names.columns = ['class', 'rtntype', 'name', 'intype', 'id']

    ## 그 두 DF의 Cartesian Product를 제작
    previous_lessons_nodes['key'] = 1
    state_names['key'] = 1
    carPro = pd.merge(previous_lessons_nodes, state_names, how='outer', on=['key'])
    carPro = carPro.drop("key", axis=1)
    carPro.columns = ['class1', 'rtntype1', 'name1', 'intype1', 'id1',
                      'class2', 'rtntype2', 'name2', 'intype2', 'id2']

    mapfunc = lambda row: scoring_function(row['id1'], row['id2'])
    
    bool_df = carPro.apply(mapfunc, axis=1)
    carPro['leave'] = bool_df

    carPro = carPro[carPro.leave != False]
    carPro = carPro.drop(columns=['leave'])

    # print(carPro)
    return carPro

# site1 = nx.read_gpickle('sagan-site_graph_1')
# make_evidence(sample_lesson, site1)
