from common_v1 import *
fixed();g=load(RUN/'compiled-readiness-graph-v1.json');ns='BanditRL.OnlineLearning.'
pairs=[(ns+'theorem_1_3',ns+'empiricalMean_minimizes'),(ns+'theorem_1_3',ns+'lemma_1_2'),(ns+'theorem_1_3','harmonic_le_one_add_log'),(ns+'meanPredict_bestRegret_refined',ns+'meanPredict_regret_refined'),(ns+'meanPredict_limitNoRegret_iff_mean_converges',ns+'meanPredict_limitNoRegret_of_mean_converges'),(ns+'dyadic_meanPredict_obstruction',ns+'meanPredict_bestRegret_average_tendsto_zero')]
selected=[]
for a,b in pairs:
    matched=[e for e in g['edges'] if e['source']==a and e['target']==b and (e['kind']=='value' or e['also_in_value'])]
    assert len(matched)==1,(a,b,matched)
    selected.append(matched[0])
write(RUN/'required-readiness-value-pairs-v2.json',dict(required_pairs=selected,all_actual_direct_VALUE_present=True,selected_compiler_edges_not_semantic_DAG_or_full_transitive_graph=True))
fixed();print('Actual direct value dependency pairs:',len(selected))
