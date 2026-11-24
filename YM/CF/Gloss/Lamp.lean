import YM.CF.Gloss.Move
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable(B)(x:Era m)
local notation "Λ"=> CSide m B
lemma cash_i(t:Sq)(a:Spot m)(z:Site (Domain m B)): cash m B (ψx B x z) t (ρi x a)=cash m B z t a:=by
 unfold cash ticks; simp [pace_v] -- cast via rfl
lemma tako(U:Skin m B)(i:Spot m)(z:Site (Domain m B))(s:Sq)(h:i∈bandS m B z s)(x_:Ballot)(o:Lattice.Order): launch m B (turnV B x U) z i.1 o (doveV x.charge x_)=dove x.charge (launch m B U (ψx B x z) (ρx x i.1) (orderEquiv x.s o) x_):=by
 have hu:= node_dist (spot_hit h); unfold launch tax; rw [armP B x _ _ ((separation_comm ..).trans_le hu.le),tag_h]; exact dove_runV ..
lemma ϕs(s:Sq)(U: Skin m B)(f:ArrayF m)(t:Site (Domain m B)): paintV m B (turnV B x U) (αRow x f) s t=dove x.charge (paintV m B U f s (ψx B x t)):=by
 let Z:=doveL x.charge; unfold paintV; have he: paint m B (turnV B x U) (αRow x f) s t=Z (paint m B U f s (ψx B x t)):=by
    unfold paint; rw [←Equiv.sum_comp (ρi x) (fun i=> cash m B _ s i • freight m B U (ψx B x t) i.1 (f i)),map_sum]; refine sum_congr rfl ?_; intro i _; rw [cash_i, map_smul]; by_cases h:i∈ bandS m B t s
    · unfold freight; rw [map_smul]; apply congrArg; apply congrArg; rw [←Equiv.sum_comp (orderEquiv x.s) (fun j=> launch m B U _ _ j _),map_sum]; exact sum_congr rfl fun j _=> tako B x U i t s h (f _) j
    rw [outside h,zero_smul,zero_smul]
 rw [he]; unfold Cube.ren; change _=Z _; rw [map_smul,LinearIsometry.norm_map]
lemma Τs{e p:ℝ}(g:enoughV B e p)(hx:0≤e)(U:Skin m B)(h:Guard U e)(H:ArrayF m)(q: Phase.Zone)(v:Sq)(hv:v∈ Phase.zone q)(s:Verified m B margin U H q): Brace.airing m B (turnV B x U) (αRow x H) v=fireA (netB m B x) (Brace.airing m B U H v):=by
 let a:=netB m B x; apply funext; intro i; apply Subtype.ext; let V:=turnV B x U; change Dial.hook _ i =_ ; rw [Brace.poet g (ζx_o B x e U h) hx ((β B x U H q).mpr s) hv,ϕs]; change _=(doveV x.charge _).val; congr 1 -- tune
 rw [ψX,← Brace.poet g h hx s hv]; rfl
end YM.CF.Gloss
