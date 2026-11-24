import YM.SU5.Selected.Cor.Charges
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
namespace Mezz
open Mint Numeric
open Stencil (pace pval pulseNode heatize)
open Caste
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
variable {N:Side} {T:Type}[Fintype T][DecidableEq T] (A:Mezz) (P:Society T)
variable (b:Bool)(i:A.Lot)(X Z:Coast→ Wq A.marks)(C:ℝ)
local notation "C₀" => cutM (Tset N)
local notation "P₀" => park N A.Broad
local notation "Q" b:max => park N (A.yard i.1 b)
local notation "T'" k:max b:max => A.pole (N:=N) P i b k X Z C
local notation "Y" => A.pole (N:=N) P i
local notation "R" => WRect (Single N) P.Club
section maskG
variable {n d:Type}[Fintype n][LinearOrder n][Fintype d][DecidableEq d]
-- C-star import. col_cont 
@[fun_prop] lemma col_dawn (i:d) : Continuous (fun F:WRect n d=> col F i):=by
 unfold col; fun_prop
@[fun_prop] lemma creed_eve (b:Bool): Continuous (creed (n:=n) b):=by cases b; exact create_cont; exact create_cont.star
@[fun_prop] lemma tape_c (b:Bool): Continuous (tape (n:=n) (q:=d) b):=by
 have h(L:List d): Continuous (fun X:WRect n d=>party (col X) b L):=by induction L with|nil=> exact continuous_const| cons i L ih=> exact ((creed_eve b).comp (col_dawn i)).mul ih
 exact h Finset.univ.toList
lemma seed_party {S T:Finset n} {A: WRect n d} (v : Contained S A)(e: hand b (cutM T)*A=A) (L:List d) : Fine T S (decide (Odd L.length)) (party (col A) b L):=by
 induction L with
 | nil=> exact Fine.one
 | cons i L h =>
    have p : (decide (Odd (i::L).length))=true.xor (decide (Odd L.length)):=by
       classical -- issue decide noncomputable classical
       by_cases z: Odd L.length <;> simp [z,Nat.odd_add_one]
    rw [p]; exact (passing _ _ ((col_lim ..).mpr e i) ((containedT ..).mp v i)).grow h
end maskG

structure Coil (F:Pane N→ WRect (Single N) P.Club): Prop where
 cont : Continuous F
 support (V:Pane N): Contained (modesIn N (Q b)) (F V)
 fixes (V:Pane N): hand b (cutM (Tset N))* F V= F V
 respect : Lattice.LocalOn (Q b) F -- signature orientation measure
namespace Coil
variable {A P i b} {F G:Pane N→ WRect (Single N) P.Club} (h:Coil A P b i F) (u:Coil A P b i G)
#print Coil.mk
include h u
lemma adds: Coil A P b i (F+G):= ⟨h.cont.add u.cont, fun x=> Contained.add (h.support _) (u.support _),fun x=> by rw [Pi.add_apply,Matrix.mul_add,h.fixes,u.fixes],fun x y p=> congrArg₂ (fun a b: Matrix _ _ ℂ => a+b) (h.respect x y p) (u.respect x y p)⟩
omit u
lemma scale (c:ℂ): Coil A P b i (c • F):= ⟨continuous_const.smul h.cont,fun x=> (h.support _).smul _,fun x=> by rw [Pi.smul_apply,Matrix.mul_smul,h.fixes],fun x y p=>congrArg (fun i:WRect _ _=>c • i) (h.respect x y p)⟩
lemma serves : AtSupport false (Q b) (fun x:Fields N=> tape b (F x.1)):= by
 apply AtSupport.fromEval (F:= fun x=> tape b (F x));
 · exact Push.SectorMeasure.Env.compact ((tape_c b).comp h.cont)
 · exact fun x y p=> congrArg _ (h.respect x y p)
 intro x; refine (show decide (Odd (Finset.univ:Finset P.Club).toList.length) = false from ?_) ▸ seed_party b (h.support x) (h.fixes x) univ.toList -- tune syntax
 rw [rung_len P.club_card]; decide
end Coil
variable {ε:ℝ}{w:ℕ}{M:Tulip.Male} (c:Caste (N:=N) A M C ε w X Z)
include c
lemma windings (k:Bool) : Coil A P b i (T' k b):= ⟨fashion A P i b k X Z C c, talent A P i b k X Z C c, pole_x A P i b k X Z C c, aura A P i b k X Z C c⟩
noncomputable def maturing : Station (park N A.Broad) A.Lot P.Club:= by
 refine ⟨fun i k V=> A.pole P i true k X Z C V.1,fun i k V=> A.pole P i false k X Z C V.1,fun i t=> ?_⟩
 let F:= A.pole (N:=N) P i; let L(b k):= F b k X Z C; let e:ℂ:= pval t; let w':=(heatize (pval t):ℂ); let Y':= e^(11:ℕ) • L true true + L true false; let Q':= w' • (e • L false true + L false false);
 let η : Buffered.Mark N := fun x => tape true (Y' x.1); let ξ : Buffered.Mark N := fun x=> tape false (Q' x.1); -- danger ω
 have ht(b k): Coil A P b i (L b k) := windings A P b i X Z C c k; have he(b): (park N (A.yard i.1 b))⊆ P₀:= image_subset_image ((A.yard_core _ _ c.value).trans A.Core_subset)
 have hY: Coil A P true i Y':= Coil.adds ((ht true true).scale _) (ht true false)
 have hQ: Coil A P false i Q':= ((ht false true).scale _ |>.adds (ht false false)).scale _
 have hs: AtSupport false P₀ (η*ξ):= (hY.serves.mono (he true)).mulM (hQ.serves.mono (he false));
 change AtSupport false P₀ (-(η*ξ)); rw [←neg_one_smul ℂ]; exact hs.smulM _
#print maturing
lemma age_low (p:Fields N)(s:Bool): (maturing A P X Z C c).low i s p=(T' s true) p.1:=rfl
lemma age_high (p:Fields N)(s:Bool): (maturing A P X Z C c).high i s p=(T' s false) p.1:=rfl
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms maturing
