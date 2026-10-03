import BanditRLProof.OnlineSubgradientDifferentiability
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
open Filter Topology Set
#check Filter.frequently_iff_neBot
#check Filter.NeBot.inf_principal
#check Filter.frequently_exists
#check Filter.eventually_inf_principal
#check tendsto_inf_left
#check tendsto_id'.mono_left
#check Tendsto.mono_left
#check le_of_tendsto_of_tendsto
#check IsCompact.tendsto_subseq'
#check tendsto_one_div_add_atTop_nhds_zero_nat
#check tendsto_inv_atTop_nhds_zero_nat
#check InnerProductSpace.toDual_symm_apply
#check EReal.continuousOn_toReal
#check isOpen_compl_singleton
