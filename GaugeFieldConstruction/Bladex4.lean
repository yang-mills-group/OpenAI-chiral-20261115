import GaugeFieldConstruction.PestrinaM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I θ E:Type}[Fintype I][LinearOrder I]{n:Side}
open Rio Grotto Isle Lattice.Corona
-- record operations $
section
variable (σ:I→ Seat n) (F:XE I (InkD n) n)(K:KK I (Copy n) n)
variable (C:BudgetPoint)(h:ℝ)(v:ℕ)(T:PI I n→ ℝ)(Y:KI I n→ℝ)(fV:BillX C σ h 1 T F)(vY:BillF C σ h 1 v Y K)
variable (ℓ η Ω a:ℝ) (b:ℕ) (P:Rio I n)(u:ℝ)(S:List I)(k:I)(X:Hub n)(l:poke_F σ X.val.2 S.toFinset)(t:σ k=X.val.1)
abbrev rental (p:ℕ)(a b:ℝ)(T: PI I n→ℝ)(Y: KI I n→ℝ) :Origin n:= fun L i=>pointX cloudP T (RedB p a b L) i+pointX cloudK Y (ColdB p a b L) i
def IncomeP(F:XE I (InkD n) n)(K:KK I (Copy n) n)(P:Rio I n):= FrameT (F+P.X+P.Y) (K+P.B)
local notation "Rm"=> rental b a η T Y
local notation "B"=> IncomeP F K P
local notation "Xp"=> B.insertΦ X σ S u k
include fV vY t
set_option maxHeartbeats 200000 in
lemma soci (pu:0 ≤u) (θ:0<η)(p: 0≤Ω)(hv:0≤h)(t0:Cube_M b*Ω≤1)(U:5*(u*Summit b a X.val.2)≤ℓ): Adv_L C σ 1 h v b a η ℓ Ω Rm (σ k) P ((IncomeP F K P).insertΦ X σ S u k) :=by
 let G':= altuQ B X S u k
 apply vintage σ G' C h 1 v (σ k) (fun i=> Eq.symm t) P (rental b a η T Y) a η ℓ Ω b p t0 zero_lt_one θ -- tune
 intro V k₀
 let A':= T+V.W+V.M; let U':=Y+V.F
 have e:A'≥0:=by intro i; exact add_nonneg (add_nonneg (fV.gist _) (k₀.white.gist _)) (k₀.active.gist _)
 have he:0≤U':=fun i=> add_nonneg (vY.gist _) (k₀.bank.gist _)
 refine ⟨(fun _=>u), A',U',e,he,fun i=> ?_,?_,fun L i=>?_⟩
 · exact salt_P (IncomeP F K P) X S ((poet S).get i) u (poet_b _ _ (List.get_mem ..)) k σ C h v A' U' (frame_r σ F K _ _ _ v _ _ fV vY P V k₀) e he hv pu (t ▸ X.property)
 · refine le_trans ?_ U; change (∑ _i: Isle.Path S,u*Summit b a X.val.2)≤_
   rw [sum_const,nsmul_eq_mul,card_univ]; unfold Isle.Path; rw [Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast poet_max S) (mul_nonneg pu (Real.exp_pos _).le)
 change _ = postG (zoneD cloudP) A' _ _ + postG (zoneD cloudK) U' _ _
 rw[pointX_π,pointX_π]
 unfold A' U'; simp only[pointX_add, rental,SumAll,Paw,Rio.Band, Pi.add_apply]; ring
end
section
-- Blank/history terms no-Fact.C.A
variable (σ:I→ Seat n) (F:XE I (InkD n) n)(K:KK I (Copy n) n)
variable (X:Hub n)(L:List I)(P:Rio I n)(μ:ℝ)(k i:I)
def BlankM (F:XE I (InkD n) n)(K: KK I (Copy n) n)(i:I):Prop:=(∀ x,F x≠0→i∉x.1)∧∀ x,K x≠0→i∉x.1
variable (V:BlankM F K i)
local notation "N"=> FrameT F K
local notation "pκ"=> insertΦ (FrameT F K) X σ L μ k
private lemma Spot {β E:Type}[Fintype β][AddCommMonoid E](S:Finset β)(f:β→ E)(p:(∑ i∈S,f i) ≠0): ∃ i∈ S,f i≠0:=by by_contra! h; exact p (sum_eq_zero h)
private lemma sparkOne {β E:Type}[Fintype β][DecidableEq β] [AddCommMonoid E](S:List I)(i:β)(f:E)(v:dues I β)(q:clipK σ i S f v ≠0): v=(S.toFinset,i)∧ f≠0:=by
 unfold clipK at q; split at q; next h=>exact ⟨h.2,q⟩
 exact False.elim (q rfl)
-- inventory.Coefficient nonzero extracts nonzero monic old inventory. Captures root placement and needed.P.Sn.
private lemma fromBank {α γ M:Type}[Fintype α][Fintype γ][AddCommMonoid M](U:Finset γ)(f:γ→ dues I α→ M)(x:dues I α)(q:(∑ i∈U,f i) x≠0):∃ i∈U,f i x≠0:= Spot U _ (show _ from fun h=> q (by rw[Finset.sum_apply]; exact h))
-- combined result per x. `pureX` and bank
include V
lemma coastline(t:i≠ k): BlankM (pureX pκ) (pκ).B i:=by
 let A:=altuQ (FrameT F K) X L μ k
 have ht(s:Sect I)(p:s∈poet L)(x: Heart X (N).UV s.reg.length) (D :Support (More n))(v:(oV (∏ j:Fin s.reg.length,(N).noteV L (boon s j) (x.val j) D))≠0) : i ∉ rosterF univ (fun j:Fin s.reg.length=>(N).purseV L (x.val j)) :=by
    intro h; obtain ⟨j,u,w⟩:= (roster_mem ..).1 h; let y:=x.val j
    have g:(N).noteV L (boon s j) y D≠0:=fun a=> v (by rw [Finset.prod_eq_zero u a]; rfl)
    have l:F y≠0:=by unfold Isle.noteV at g; split at g; exact g; contradiction
    exact V.1 (x.val j) l ((mem_sort ..).1 (List.mem_filter.mp w).1) -- tune
 constructor
 · intro r q h; rw[κpClip] at q; obtain ⟨j,_,m⟩:= fromBank _ _ r q; change Rinc σ (A j) r≠0 at m; let s:= (poet L).get j; let b:=A j
   unfold Rinc at m; obtain ⟨x,e,u⟩:= fromBank _ _ r m; obtain ⟨p,q⟩:=sparkOne σ _ _ _ r u; rw [p] at h; obtain a:=List.mem_toFinset.mp h; split at q; swap
   next v =>
       have hO:(oV (∏ l:Fin s.reg.length,(N).noteV L (boon s l) (x.val l) ∅))≠0:=by
          intro o; apply q; have hx:(∏ l:Fin s.reg.length,(N).noteV L (boon s l) (x.val l) ∅)=0:=by
             funext y; let g:=congrFun o (y,fun _=>(0,1,1)); exact g -- Ids n need type.Nonempty
          change μ • _= _; rw[hx,smul_zero]
       exact (ht s (List.get_mem ..) x ∅ hO) ((List.mem_cons.mp a).resolve_left t)
   contradiction
 intro r q h; change (∑ j, Kinc σ (A j)) r ≠ 0 at q
 obtain ⟨j,_,g⟩:= fromBank _ _ r q; unfold Kinc at g; obtain ⟨x,b,w⟩:=fromBank _ _ r g; obtain ⟨y,u,p⟩:=fromBank _ _ r w; obtain ⟨p,w⟩:=sparkOne σ _ _ _ r p; rw[p] at h; let P:=y.val; let s:=(poet L).get j
 let D:= oV (∏ l:Fin s.reg.length,(N).noteV L (boon s l) (x.val l) (til (N).U P)); let V':=(N).oracle L s P; change μ • (D*V')≠0 at w
 have hD:D≠0:= fun e=>w (by rw[e,zero_mul,smul_zero]); have hv:V'≠0:=fun e=>w (by rw[e,mul_zero,smul_zero]); rcases List.mem_append.mp ((List.mem_cons.mp (List.mem_toFinset.mp h)).resolve_left t) with v|v
 · exact ht s (List.get_mem ..) x _ hD v
 obtain ⟨l,h,u⟩:= (roster_mem ..).1 (List.mem_filter.mp v).1; unfold V' oracle at hv; split at hv; swap; · contradiction
 exact V.2 l (fun e=>hv (prod_eq_zero h e)) ((mem_sort ..).1 u)
omit V
-- each produced term on k located and anchored. List.#unchanged.
lemma staffKY : (∀ x:PI I n,pureX pκ x≠0→k ∈ x.1 ∧ X.val.1=x.2.val.1 ∧ X.val.2⊆ cloudP x.2) ∧∀ x:KI I n,(pκ).B x≠0→k∈x.1:=by
 let A:=altuQ (FrameT F K) X L μ k
 constructor
 · intro x q; rw[κpClip] at q; obtain ⟨i,_,t⟩:=fromBank _ _ x q; unfold Rinc at t; obtain ⟨i,l,b⟩:=fromBank _ _ x t; rw[(sparkOne σ _ _ _ x b).1]; exact ⟨List.mem_toFinset.mpr (List.mem_cons_self ..),rfl,subset_union_left⟩
 intro x p; change (∑ i: Isle.Path L,Kinc σ (A i)) x ≠0 at p
 obtain ⟨i,_,w⟩:= fromBank _ _ x p; unfold Kinc at w; obtain ⟨i,h,w⟩:=fromBank _ _ x w; obtain ⟨t,l,q⟩:=fromBank _ _ x w; rw[(sparkOne σ _ _ _ x q).1]; exact List.mem_toFinset.mpr (List.mem_cons_self ..)
#print axioms coastline
end
end Iona
end YM.CF.Scree.Ing
end
