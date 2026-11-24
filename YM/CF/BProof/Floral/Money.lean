import YM.CF.BProof.Floral.Prop
import YM.CF.BProof.Floral.Pit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{p:BudgetPoint} {X:Hub n}{Y:Force n}{F:ℂ→InkD n}{E:ℂ→ Copy n}{a h L:ℝ}
open Forge
variable (u:1<L)(k:1≤h)
include u k
lemma pea (T:∀ z∈disk L,PressB p X (F z) h a)(H:∀ U: Pane n,pingS p.threshold X.val.2 U→ Hol (disk L) fun z=> F z U): Rule fun (x:Points L) c=> PressB p X (pick F x) h c:=by
 let s:Set (Pane n):={U|pingS p.threshold X.val.2 U}; let V:= Finset (Dwell n); let c(i:V):= tariff p X.val.1 h i
 let e(i:V)(x:Points L)(U:Pane n)(y:tangD n):= chipV i (pick F x (increment U y)); let Q(i:V):Cost L:=fun x b=> 0 ≤ b ∧ ∀ U:s, Signs p X.val.1 (e i x U) b
 have hh(U: Pane n): gyrate univ U=increment U:= funext fun i=> congrArg (increment U) (show wakeB univ i=i from funext fun x=> by rw [steadyB,if_pos (mem_univ _)])
 have ht(i:V):Rule (Q i):=by
    let f(z:ℂ)(U:Pane n):= chipV i (F z U); have hu(U:Pane n)(z:Points L) : e i z U= pick (fun t=> f t ∘ gyrate univ U) z:=by rw [hh U]; cases z <;> rfl
    have hv(y)(f':y∈s)(z)(p':z∈disk L): Signs p X.val.1 (f z ∘ gyrate univ y) a:=by rw [hh]; exact press_high (T z p') k _ f' i
    have hs(U:s):Rule (fun x b=>Signs p X.val.1 (e i x U) b):=by simp_rw [hu U]; exact bed_rule ping_o hv (fun y h'=> (chipV i).differentiable.comp_differentiableOn (H y h')) u U U.property
    exact Rule.max_cost hs
 refine (Rule.sigma Finset.univ c Q (fun i _=> zero_lt_one.trans_le (tariff_high i _ k)) (fun i _=> ht i)).rose fun x C=> ?_
 have w: ∃ a, PressB p X (pick F x) h a:= match x with | none=>⟨_,regular_sub (T 1 (d1 u)) (T 0 (d0 u))⟩ | some i=>⟨_, T i i.property⟩
 obtain ⟨a0,j,g,q,f,-⟩:=w
 constructor
 · rintro ⟨b,h,t⟩; exact ⟨j,g,q,f,b,fun i=>(h i (mem_univ _)).1,fun U u i=> (h i (mem_univ i)).2 ⟨U,u⟩,t⟩
 intro p; obtain ⟨b,v,y,t⟩:=p.worth; exact ⟨b,fun i _=> ⟨v i,fun U=> y _ U.property i⟩,t⟩
lemma silk (T:∀ z∈disk L,ForceB p Y (E z) h a)(H:∀ U: Orbit n,pingS p.threshold (Y.val.1.val.2\Y.val.2) U.1→ Hol (disk L) fun z=> E z U): Rule fun (x:Points L) c=> ForceB p Y (pick E x) h c:=by
 let s:= {U:Orbit n// pingS p.threshold (Y.val.1.val.2\Y.val.2) U.1}; let V:= Finset (Dwell n); let c(i:V):= tariff p Y.val.1.val.1 h i
 let e(i:V)(x:Points L)(U:Orbit n)(y:tangD n):= chipV i (pick E x (increment U.1 (openG p Y.val.2 y),U.2)); let Q(i:V): Cost L:=fun x b=> 0 ≤ b ∧ ∀ U:s, Signs p Y.val.1.val.1 (e i x U.val) b
 let S:Set (Pane n):={U|pingS p.threshold (Y.val.1.val.2\Y.val.2) U}; let I:= Rill.unrest Y.val.2 p.B
 have ht(i:V)(U:s):Rule fun (x:Points L) b=> Signs p Y.val.1.val.1 (e i x U.val) b:=by
    let f(z:ℂ)(y:Pane n):= chipV i (E z (y,U.val.2)); have hj(y:Pane n)(z): f z ∘ gyrate I y=fun t=> chipV i (E z (increment y (openG p Y.val.2 t),U.val.2)):=by simp_rw [Rill.padP]; rfl
    have hv(y)(f':y∈S)(z)(p':z∈disk L): Signs p Y.val.1.val.1 (f z ∘ gyrate I y) a:=by rw [hj]; exact force_high (T z p') k (y,U.val.2) f' i
    have hc: ∀ x,e i x U.val= pick (fun t=>f t ∘ gyrate I U.val.1) x:=by simp_rw [hj]; intro x; cases x <;> rfl
    simp_rw [hc]; exact bed_rule ping_o hv (fun y h'=> (chipV i).differentiable.comp_differentiableOn (H (y,U.val.2) h')) u U.val.1 U.property
 refine (Rule.sigma Finset.univ c Q (fun i _=> zero_lt_one.trans_le (tariff_high i _ k)) (fun i _=> Rule.max_cost (ht i))).rose fun x C=> ?_
 have w: ∃ a, ForceB p Y (pick E x) h a:= match x with | none=>⟨_,force_sub (T 1 (d1 u)) (T 0 (d0 u))⟩ | some i=>⟨_, T i i.property⟩
 obtain ⟨a0,j,g,q,f,l,m,-⟩:=w
 constructor
 · rintro ⟨b,h,t⟩; exact ⟨j,g,q,f,l,m,b,fun i=>(h i (mem_univ _)).1,fun U u i=> (h i (mem_univ i)).2 ⟨U,u⟩,t⟩
 intro p; obtain ⟨b,v,y,t⟩:=p.costP; exact ⟨b,fun i _=> ⟨v i,fun U=> y _ U.property i⟩,t⟩
end YM.CF.Floral
