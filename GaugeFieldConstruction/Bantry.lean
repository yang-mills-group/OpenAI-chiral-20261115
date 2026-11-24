import GaugeFieldConstruction.Nepal
import YM.CF.Rill.Pott
import YM.CF.Proa.Uta
import YM.CF.Broc.Loci
import YM.CF.Rue.Salt
import YM.CF.Floe.Ton
import YM.CF.Floe.Paid
/- Link and frame tags used for X2. Witness locality bills. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF
namespace XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes
variable {K b c d r v e:ℝ}{N m B:Side}{n:ℕ}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
abbrev Clode (N:Side)(e:ℝ):Set (Pane N):= interior {A| Guard A e}
abbrev Lobby (m B:Side)(e:ℝ):Set (Skin m B × Cue m):={x|x.1∈Clode (CSide m B) e∧Phase.law m B x.1 x.2≠0}
lemma grow_I {x:Pane N}(h:Guard x e)(p:e<r):x∈ Clode N r:=mem_interior_iff_mem_nhds.mpr (Rill.walkL _ x h p)
lemma lobby_G {x:Skin m B × Cue m}(h:x∈ Lobby m B e): Guard x.1 e ∧ ZeroF m B x.1 x.2:=⟨interior_subset (s:={x:Pane (CSide m B)|Guard x e}) h.1,law_rich m B x.1 x.2 h.2⟩
lemma lobby_o:IsOpen (Lobby m B e):= (isOpen_interior.preimage continuous_fst).inter ((isClosed_eq (law_cont m B) continuous_const).isOpen_compl)
lemma cliff_n {q:E→Bkg N}{x:E}(h:TransK n q x K):ContinuousAt q x:=by
 apply continuousAt_pi.mpr; intro i; exact (SU.fund_cont.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (h i).smooth.continuousAt
lemma stream_T {U:E→Bkg N}{x:E}(h:TransK n U x K)(g:K<b): ∀ᶠ t in 𝓝 x,TransK n U t b:=by
 exact eventually_all.mpr fun i=> by
    let f(t:E):=SU.fund (U t i); have hp:=h i; have hs (j: Fin (n+1)):∀ᶠ t in 𝓝 x,‖iteratedFDeriv ℝ (j:ℕ) f t‖≤b:=(((hp.smooth.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt))).norm).eventually (gt_mem_nhds ((hp.norm_le j (Nat.le_of_lt_succ j.isLt)).trans_lt g))).mono fun i v=> LE.le.trans (LT.lt.le v) le_rfl
    filter_upwards [eventually_all.mpr hs,hp.smooth.eventually (by simp)] with i hs g; exact ⟨g,fun j v=>hs ⟨j,Nat.lt_succ_of_le v⟩⟩
section
-- functions with Cue involved. cost even MOVEMENT F stands in BOTH arguments.
abbrev Pantry (m B:Side):Type:=Skin m B × Cue m
abbrev SheetT (m B:Side):Type:= Pantry m B → ℂ
variable {W:Type}[NormedAddCommGroup W][NormedSpace ℝ W]
structure Ka (K:ℝ) (n:ℕ) (e:ℝ)(V:Support (Domain m B))(F:Pantry m B→ W)(C:ℝ) : Prop where
 pos: 0 ≤ C
 ct: ContinuousOn F (Lobby m B e)
 watch: ∀ x∈ Lobby m B e,∀ y∈ Lobby m B e, Lattice.Agrees V x.1 y.1→Phase.Sample.AgreeF (complexA m B V) x.2 y.2→ F x= F y
 track :∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:E→Skin m B)(x:E)(i:Cue m),(U x,i)∈ Lobby m B e → TransK 7 U x K → Allows n (fun v=>F (U v,i)) x C
variable {f g: Pantry m B→W} {U T V : Support (Domain m B)}
namespace Ka
lemma scaleUp (h:Ka K n e V f c)(p:c≤ b): Ka K n e V f b:= ⟨h.pos.trans p,h.ct,h.watch,fun E _ _ _ U x i t u=>(h.track E U x i t u).mono p⟩
lemma narrow (h:Ka K n e V f c)(p:b≤K):Ka b n e V f c:=⟨h.pos,h.ct,h.watch,fun E _ _ _ U x i t u=> h.track E U x i t fun j=>(u j).mono p⟩
lemma tin (h:Ka K n e U f c)(p:U ⊆ V): Ka K n e V f c:= ⟨h.pos,h.ct,fun x hx y hy l w=> h.watch x hx y hy (fun i j k=>l i (p j) (p k)) (fun i g=> w i (complex_up m B p g)), h.track⟩
lemma lower {j:ℕ}(h:Ka K n e U f c)(l:j≤ n):Ka K j e U f c:= ⟨h.pos,h.ct,h.watch,fun E _ _ _ F x i t u=> (h.track E F x i t u).order l⟩
lemma add_H (h:Ka K n e V f c)(p:Ka K n e V g d):Ka K n e V (fun x=> f x+ g x) (c+d):= ⟨add_nonneg h.pos p.pos,h.ct.add p.ct,fun x v y t u q=> congrArg₂ (·+·) (h.watch _ v _ t u q) (p.watch _ v _ t u q),fun E _ _ _ F x i t u=> (h.track E F x i t u).add (p.track E F x i t u)⟩
lemma neg_H (h:Ka K n e V f c):Ka K n e V (fun x=> -f x) c:=⟨h.pos,h.ct.neg,fun x v y t u q=> congrArg (- ·) (h.watch _ v _ t u q),fun E _ _ _ F x i t u=>by simpa using (h.track E F x i t u).smul (-1)⟩
variable {W':Type}[NormedAddCommGroup W'][NormedSpace ℝ W']
lemma maps_H (h:Ka K n e V f c)(L:W→L[ℝ] W')(p:‖L‖≤d):Ka K n e V (fun x=> L (f x)) (d*c):=⟨mul_nonneg ((norm_nonneg _).trans p) h.pos,L.continuous.comp_continuousOn h.ct,fun x v y t u e=> congrArg L (h.watch _ v _ t u e),fun E _ _ _ F x i t u=> (h.track E F x i t u).linear _ p⟩
abbrev β_H (n:ℕ):ℝ:= 2^n*‖ContinuousLinearMap.mul ℝ ℂ‖
lemma mul_H {f g:SheetT m B}(h:Ka K n e V f c)(p:Ka K n e V g d):Ka K n e V (fun x=> f x*g x) (β_H n*c*d):= ⟨by unfold β_H; have hv:=h.pos; have ht:=p.pos; positivity,h.ct.mul p.ct,fun x v y t u e=> congrArg₂ _ (h.watch _ v _ t u e) (p.watch _ v _ t u e), fun E _ _ _ F x i t u=> Allows.bilinear (ContinuousLinearMap.mul ℝ ℂ) (h.track E F x i t u) (p.track E F x i t u) le_rfl⟩
lemma zero_H : Ka K n e V (fun _:Pantry m B=> (0:W)) 0:= ⟨le_rfl,continuousOn_const,fun _ _ _ _ _ _=>rfl,fun _ _ _ _ _ _ _ _ _=> allows_const _ (norm_zero.le)⟩
lemma sumH {I:Type*} (s:Finset I)(F:I→ Pantry m B→ W)(C:I→ℝ)(h:∀ i∈s,Ka K n e V (F i) (C i)):Ka K n e V (fun x=>∑ i∈s,F i x) (∑ i∈s,C i):=⟨sum_nonneg fun i p=>(h i p).pos,continuousOn_finsetSum _ fun i p=>(h i p).ct,fun x p y u v e=>sum_congr rfl fun i g=>(h i g).watch _ p _ u v e,fun E _ _ _ U x i t u=> allows_sum fun j g=> (h j g).track E U x i t u⟩
end Ka
end
end XGarden
end YM.CF
end
