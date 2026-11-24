import YM.CF.Sour.Vill
import YM.CF.Ione.Tape
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
-- real quarry stitches, frame max constants preserve before.L. Only Real lemma Focus perf stencils, new Lawn.s sigma orientation.Open τ.
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
structure Elm(N:Side)(κ:Type)[TopologicalSpace κ](d e v:ℝ) where
 F:Support (More N)→κ→Raw (Openc (More N) d) (Single N)
 W:Support (More N)→Toll (Single N)
 coat:∀ S,pendB (badge _) (bail N d) (bail N d) (F S) S (W S)
 bank:Ledger e W v
variable {d e v:ℝ}(E:Elm n κ d e v)(F:κ→BeatL n)
def condB(n:Side)(d:ℝ):= {x :↥(Openc (More n) d)//∃ V: Pane n, x.val=Tulip.profile V} -- too expensive? later.
abbrev Seen (E:Elm n κ d e v)(F:κ→BeatL n):Prop:=∀ i,∀ (x:↥(Openc (More n) d)),∀ V:Pane n,x.val=Tulip.profile V → F i x.val=∑ S,E.F S i x
lemma bolt_e {N:Side}{K:Gem N κ}(X:Lawn N d K e v):Seen (⟨X.F,X.W,X.coat,X.store⟩:Elm N κ d e v) K:=fun i x _ _=> X.shape i x
lemma real_f {ι:Type*}(s:Sweep n)(b:Bool)(S:Finset ι)(F:ι→ Op JS): realR s b (∑ i∈S,F i)=∑ i∈S,realR s b (F i):=by cases b <;> by_cases p:detX s.s <;>simp only [realR,bolt,foeL,Sault.hitL,Sault.doveL,Thera.jazz, p,ite_false,Bool.false_eq_true,ite_true, singT,win_sum,map_sum,star_sum,sum_neg_distrib] -- binder
lemma real_t (s:Sweep n)(b:Bool)(r:ℝ)(F: Op JS): realR s b ((r:ℂ) • F) =(r:ℂ) • realR s b F:=by cases b <;>by_cases p:detX s.s <;>simp [realR,bolt,foeL,Sault.hitL,Sault.doveL,Thera.jazz,p,Complex.coe_smul]
def Elm.Utar (b:Bool): Elm n κ d e (Tenant.quota^2*v):= ⟨fun S i=>trackV s b d (E.F (actY s S) i),testV s b E.W,veil s d E.W b E.coat,wardK s d E.W b E.coat E.bank⟩
variable (b0:Bool)
local notation "Sv"=> s
lemma real_box (W:Pane n)(t:↥Ω)(q:t.val=Tulip.profile W): (Sour.fog s a t).val=Tulip.profile (flashA s W):=by unfold fog; dsimp only; rw [q]; exact (veil_p ..).symm
lemma Elm.wren(X:SO)(i:κ)(W:Pane n)(t:Openc (More n) d)(p:t.val= Tulip.profile W): (E.Utar s b0).F X i t=realR s⁻¹ b0 (E.F (actY s X) i (Sour.fog s d t)):= tiles s d b0 t W p _ -- tune
variable {η:Type} {c:ℝ}
lemma Elm.turn(H: Seen E F)(u:κ→ BeatL n)(R:∀ i (x:↥(Openc (More n) d)),∀ V:Pane n,x.val=Tulip.profile V → realR s⁻¹ b0 (F i (Sour.fog s d x).val)=u i x.val):Seen (E.Utar s b0) u:=by
 intro i x V p; rw [←R _ _ _ p,H _ _ _ (real_box s d V x p),real_f]
 symm; refine sum_bij (fun x _=>actY s x) (fun _ _=>mem_univ _) (fun i _ j _ k=>map_injective _ k) (fun i _=>⟨actY s⁻¹ i,mem_univ _,?_⟩) (fun w _=>?_)
 · ext; simp [actY,sitU]
 rw [E.wren s b0 w _ _ _ p]
-- add arbitrary broadcasts.
def Elm.zero0(d e:ℝ):Elm n κ d e 0:= ⟨0,0,fun S=> ⟨fun i=>Suite.free _,fun x=>continuous_const⟩,⟨le_rfl,fun i=>by simp [saleM],fun i=>by simp [saleM]⟩⟩ -- `lemma` should def
abbrev weave (p:ℝ):=Real.exp p
def Elm.plus(B:Elm n κ d e c):Elm n κ d e (v+c):=⟨E.F+B.F,E.W+B.W,fun i=>⟨fun j=> (E.coat i|>.1 j).plus (B.coat i|>.1 j),fun x=>(E.coat i|>.2 x).add (B.coat i|>.2 x)⟩,E.bank.pairT B.bank⟩
lemma drum_p {ι:Type}(S:Finset ι)(P:ι→Elm n κ d e v): Ledger e (∑ s∈S,(P s).W) (∑ _∈S,v):=by
 induction S using Finset.induction_on with
 |empty=> simp only [sum_empty]; exact (Elm.zero0 (n:=n) (κ:=κ) d e).bank
 |insert i S p ih=> rw [sum_insert p,sum_insert p]; exact (P i).bank.pairT ih
lemma port_p {ι:Type}(S:Finset ι)(P:ι→Elm n κ d e v)(X:SO): pendB (badge _) (bail n d) (bail n d) (fun i x=> ∑ s∈ S,(P s).F X i x) X ((∑ s∈ S,(P s).W) X):=by
 induction S using Finset.induction_on with
 |empty=> simp only [sum_empty]; exact (Elm.zero0 (n:=n) (κ:=κ) d e).coat _
 |insert i S p ih=> simp_rw [sum_insert p]; exact ⟨fun j=>(P i|>.coat X|>.1 j).plus (ih.1 j),fun x=>(P i|>.coat X|>.2 x).add (ih.2 x)⟩
abbrev avg(n:Side):ℝ:=(Fintype.card (Sweep n):ℝ)⁻¹
local notation "Lv"=> avg n
lemma avg_s{B:Type*}[AddCommGroup B][Module ℂ B](A:B): (Lv:ℂ) • (Fintype.card (Sweep n) • A)= A:=by
 rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul]; unfold avg; have hp:= Fintype.card_pos (α:=Sweep n); push_cast; rw [inv_mul_cancel₀,one_smul]; exact_mod_cast (Nat.ne_of_gt hp)
-- Sund.Aver. 
def chime (P:Sweep n→Elm n κ d e v):Elm n κ d e v:=by
 let Z:= ∑ i:Sweep n,(P i).W
 refine ⟨fun X i x=>(Lv:ℂ) • (∑ s:Sweep n,(P s).F X i x),fun X i j=>‖(Lv:ℂ)‖*Z X i j,fun X=>⟨fun i=>(port_p univ P X|>.1 i).accel _,fun x=>(continuous_const (y:=(Lv:ℂ))).smul (port_p univ P X|>.2 x)⟩,?_⟩
 have ht:= (drum_p univ P).funds (norm_nonneg (Lv:ℂ)); rw [Complex.norm_real,Real.norm_of_nonneg ?q,sum_const,nsmul_eq_mul, ←mul_assoc,card_univ] at ht; swap; · unfold avg; positivity
 rw [avg,inv_mul_cancel₀,one_mul] at ht
 simp_rw [Complex.norm_real,Real.norm_of_nonneg (show 0≤Lv from (by unfold avg; positivity))]; exact ht
 positivity
lemma seen_K (P:Sweep n→Elm n κ d e v)(r:∀ i,Seen (P i) F):Seen (chime P) F:=by
 intro i x V h; change _= ∑ Y:SO,(Lv:ℂ) • (∑ k:Sweep n,(P k).F Y i x); rw [←smul_sum,sum_comm]; simp_rw [←show ∀ k:Sweep n,F i x.val= _ from fun k=>r k i x V h,sum_const,card_univ]; rw [avg_s]
end YM.CF.Sour
