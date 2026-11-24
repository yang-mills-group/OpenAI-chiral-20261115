import GaugeFieldConstruction.Quality
/-!
# Capped raw frames onto the on-shell fields
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration.RawBank
open Cauchy Row Record Phys Stage Stage.Cell Stage.Wide Function Filter Set Complex Conj LabelAction Submodule Floor
open Flux One One.Lamp -- order
open scoped BigOperators
variable {α β γ η V : Type*}

structure Mint (R : Record β V) (H : Submodule ℂ (J β)) (F : Flip β) (α : Type*) [Fintype α] where
  label : Labels α
  q : α→ J β
  sale: space q=H
  set : R.Reading label q
  actual :∀ i,F (q i)=q i

namespace Mint
variable [Fintype α] [Fintype γ] {R : Record β V} {H U : Submodule ℂ (J β)} {F : Flip β}
    (B : Mint R H F α) (C : Mint R U F γ)
def left (e : H=U): Mint R U F α := {B with sale:=B.sale.trans e}
def cup : Mint R (H⊔U) F (α ⊕ γ) where
  label:=B.label.directSum C.label
  q:=Sum.elim B.q C.q
  sale:=by rw [space_sum,B.sale,C.sale] -- namespace
  set:= reading_add B.set C.set
  actual i:= match i with
    | Sum.inl i=>B.actual i
    | Sum.inr j=>C.actual j
lemma ability (w : J α): jet B.q w∈H := by
  induction w using Finsupp.induction_linear with
  | zero=> simp
  | add w p h k=> rw [map_add]; exact H.add_mem h k
  | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket], map_smul,on_ket]; exact H.smul_mem _ (B.sale.le (range_sets B.q i))

def issue : J α →ₗ[ℂ] H := (jet B.q).codRestrict _ B.ability
lemma supply : Surjective B.issue := by
  rw [← LinearMap.range_eq_top]; apply top_unique; rintro i _
  suffices s : H ≤ LinearMap.range (jet B.q) by
    obtain ⟨w,e⟩:=s i.property; exact ⟨w,Subtype.ext e⟩
  refine le_trans B.sale.ge ?_; rw [space,Fintype.range_linearCombination]; apply span_le.mpr; rintro _ ⟨v,rfl⟩; exact ⟨ket v,on_ket ..⟩
lemma respect [DecidableEq α] (A : Carries R H) (s : Signed) (z) : issue B (beacon B.label s z)= A.moves s (issue B z) := by
  have ht: issue B ∘ₗ beacon B.label s=A.moves s ∘ₗ issue B:= by
    refine @ket_ext α H (@Submodule.addCommGroup ℂ (J β) _ _ _ H) _ (issue B ∘ₗ beacon B.label s) (A.moves s ∘ₗ issue B) fun i => ?_; apply Subtype.ext; apply ext_jet R.faith; intro w
    obtain ⟨u,p⟩:= R.permit s w
    simp only [LinearMap.comp_apply] -- adjust
    rw [← A.transit p]; change R.tester w (jet _ (beacon _ _ _))= R.tester u (jet _ _)
    rw [on_ket,B.set.moving s w u p,beacon,on_ket]; cases B.label.cost s i <;> simp
  exact LinearMap.congr_fun ht _
lemma paid_at (i:α): (issue B (ket i)).val=B.q i:= on_ket ..
lemma real (x : J α) : F (jet B.q x)=jet B.q (tr α x) := by
  have h : F ∘ₛₗ jet B.q=jet B.q ∘ₛₗ tr α:=ksets fun i=>by rw [LinearMap.comp_apply,LinearMap.comp_apply,on_ket, tr_ket,on_ket,B.actual]
  exact LinearMap.congr_fun h x
end Mint

open Raw
open U1 (ph)

def BoxG : Floor → Type | three=> Empty| four=>GE|five=>GE ⊕ G1
def BoxF : Floor→Type| three=>PH|four=>PH⊕T1|five=>(PH⊕T1)⊕ T2
def BoxX : Floor→Type| three=>Empty|four=>Empty|five=>MX
instance dg (d : Floor): DecidableEq (BoxG d):= match d with | three=>inferInstanceAs (DecidableEq Empty)| four=>inferInstanceAs (DecidableEq GE)|five=>inferInstanceAs (DecidableEq (GE⊕G1))
set_option synthInstance.maxSize 4000
set_option maxRecDepth 1500
instance df (d : Floor): DecidableEq (BoxF d):= match d with | three=>inferInstanceAs (DecidableEq PH)|four=>inferInstanceAs (DecidableEq (PH⊕T1))|five=>inferInstanceAs (DecidableEq ((PH⊕T1)⊕T2))
instance dx (d : Floor): DecidableEq (BoxX d):= match d with | three=>inferInstanceAs (DecidableEq Empty)|four=>inferInstanceAs (DecidableEq Empty)|five=>inferInstanceAs (DecidableEq MX)
instance kg (d : Floor) : Fintype (BoxG d):=match d with| three=>inferInstanceAs (Fintype Empty)|four=>inferInstanceAs (Fintype GE)|five=>inferInstanceAs (Fintype (GE⊕G1))
instance kf (d : Floor) : Fintype (BoxF d):=match d with| three=>inferInstanceAs (Fintype PH)|four=>inferInstanceAs (Fintype (PH⊕T1))|five=>inferInstanceAs (Fintype ((PH⊕T1)⊕T2))
instance kx (d : Floor) : Fintype (BoxX d):= match d with| three=>inferInstanceAs (Fintype Empty)|four=>inferInstanceAs (Fintype Empty)|five=>inferInstanceAs (Fintype MX)

-- Reuse program runs as raw basis.

def stub (R : Record β V) (F : Flip β) : Mint R ⊥ F Empty := {
  label:= Labels.unitL _
  q := fun v => nomatch v
  sale:= by unfold space; rw [Fintype.range_linearCombination,Set.range_eq_empty,span_empty]
  set:=⟨fun s w u h i=>i.elim⟩
  actual i:=i.elim }
lemma tr_sheet (i: W): tr GIndex (sheet i)=sheet i:=by
  -- restrict complex semilinear? simpler ordinary raw
  rcases i with ⟨i,j⟩; rcases lt_trichotomy i j with h|h|h
  · exact realistic (Wed.mk _ _ h)
  · rw [h]; simp [sheet,U1.Gauge97.zero_angle]
  change tr _ (F i j)=_; rw [U1.Gauge97.turnover i j]; unfold sheet; rw [map_neg, U1.Gauge97.turnover i j]; exact congr_arg Neg.neg (realistic (Wed.mk _ _ h))
def gCard (d : Floor): Cell (BoxG d):=match d with
  | three=> Cell.Still Empty
  | four=>PG
  | five=> Cell.sum PG PG1
def fCard (d : Floor): Cell (BoxF d):=match d with|three=>Cell.UnitV|four=> Cell.sum Cell.UnitV PT1|five=>Cell.sum (Cell.sum Cell.UnitV PT1) PT2
def xCard (d : Floor) (p q : Bool) : Cell (BoxX d):=match d with|three=>Cell.Still Empty|four=>Cell.Still Empty|five=>PX p q

def G4b : Mint recG (space evalTg) cG GE := ⟨leaf4,page,pagesG, leafR,fun i=>by simp [page,cG,Bose,portal,tr_sheet]⟩
private lemma star1 (x:G1) : cG (pageV x)=pageV x := by
  have he p i: (tr GIndex) (Gder i (sheet p))=Gder i (sheet p) := Eq.trans (LinearMap.congr_fun (Gmoves i) (sheet p)) (congr_arg (Gder i) (tr_sheet p))
  simp [pageV,cG,Bose,portal,tr_sheet,he]
def G5b : Mint recG (space evalG) cG G1:=⟨leaf5,pageV,pagesH, leafV,star1⟩
def DeckG (d:Floor):Mint recG (SG d) cG (BoxG d):=match d with
  | three=> stub recG cG
  | four=> G4b
  | five=>G4b.cup G5b
def FB : Mint ph (space Row.B) cF PH:= ⟨Raw.f3Act, Row.B,rfl, readingB, f3_tr⟩
def F1 : Mint ph (space evalTf) cF T1:=⟨Raw.f4Act,evalTf,rfl,readingTf,f4_tr⟩
def F2 : Mint ph (space evalF) cF T2:=⟨stem5,foldP,pagesF,stem,by
  rintro ⟨i,g|v|q⟩ <;> simp only [foldP,Sum.elim_inl,Sum.elim_inr,cL,f_tr, f3_tr]⟩
def DeckF (d:Floor):Mint ph (SF d) cF (BoxF d):= match d with
 
  | three=>FB
  | four=> FB.cup F1
  | five=>(FB.cup F1).cup F2
def X5p:Mint recX (space evalX) cX MX:=⟨horse,Wide.log,pagesX,X_stamp,fun i=>by rw [Wide.log,cX,portal, tr_sheet,f3_tr]⟩
def DeckX (d : Floor):Mint recX (SX d) cX (BoxX d):=match d with|five=>X5p|three=>stub recX cX|four=>stub recX cX
lemma appG (i:Floor): Fast (DeckG i).label (gCard i) := by cases i with
                                                                       | three=> exact vacs (Labels.unitL Empty)
                                                                       | four=>exact fG1
                                                                       | five=>exact fast_sum fG1 fG2
lemma fromG (i:Floor): Match (DeckG i).label (gCard i) := by
  cases i
  · change Match (Labels.unitL Empty) _
    intro s e i; exact Subsingleton.elim ..
  · exact mG1
  exact match_sum mG1 mG2
lemma appF (i:Floor): Fast (DeckF i).label (fCard i) := by cases i with
                                                                | three=>exact fP
                                                                | four=>exact fast_sum fP fQ
                                                                | five=>exact fast_sum (fast_sum fP fQ) fR
lemma fromF (i:Floor) : Match (DeckF i).label (fCard i):= by
  cases i
  · exact mP
  · exact match_sum mP mQ
  exact match_sum (match_sum mP mQ) mR
lemma appX (i:Floor) (p q):Fast (DeckX i).label (xCard i p q):= by cases i with
                                                                     | five=>exact fX p q
                                                                     | _=>exact vacs (Labels.unitL Empty)
lemma fromX (i:Floor): Match (DeckX i).label (xCard i true true):= by
  cases i with
  | five=>exact mX
  | three|four=>
    change Match (Labels.unitL Empty) _; intro s h i; exact Subsingleton.elim ..
end YM.GaugeFieldConstruction.Calibration.RawBank
