import GaugeFieldConstruction.Calipers
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open SelectionAnalysis
namespace Porch
variable {I:Type*}{P:Spine}{j:Axis}{cost:ℕ→P.Test→ℂ}(R:Porch P cost j)
variable {F : I→P.Test}{U W:I→ marks (timeMesh P.par)}{A:I→P.Slabs j}
local notation "π"=> P.stampPin
local notation "M"=> timeMesh P.par
local notation "T"=> R.Time.E
local notation "Ω"=> R.Ω
local notation "Hβ"=> P.HabBox j
local notation "G"=> R.elementals U W
local notation "χ"=> P.shifts j
local notation "η"=> R.ρ

section
variable {s:ℕ}(hw:∀ i: I, 0 < (W i:ℝ))
/-- No projections: each visiting operator when posed on ticks and each wall
 by a mesh increment is THE shifted finite-height price. -/
lemma at_mesh {k:I}(v:Cover){a:ℤ}{w:ℕ}{F:P.Test}
    (p:(π s a)=P.vtile s v j-U k)(q:π s w=W k)
    (t:P.BEntry j w (χ (- (a-v j)) F))(e:A k= Hβ s w (χ (- (a-v j)) F)):
    P.BEntry j w (χ (-a) (P.chartAll v F)) ∧
      ((G hw A).visiting (η (A k)) (P.vtile s v))=η (Hβ s w (χ (-a) (P.chartAll v F))) :=by
 obtain ⟨u,h⟩:=R.meshM_turn (s:=s) t v
 rw [sub_add_cancel] at u h
 change _ ∧ R.porchMove (P.vtile s v)*(η (A k)* R.porchMove (-(P.vtile s v)))=_
 refine ⟨u,?_⟩; rw [←mul_assoc,e,h]

variable (t:ℕ) (a:I→ℤ)(w:I→ℕ)(g:I → Cover)
abbrev pins (P:Spine)(i:I) : P.VMark:=P.vtile t (g i)
def poseTiles (P:Spine)(g:I → Cover)(F:I→P.Test)(l:List I):P.Test:= (l.map (fun i=>P.chartAll (g i) (F i))).prod
local notation "bspin" => poseTiles P g F
local notation "θ" i:max=> P.vtile t (g i)
local notation "fΛ" => Repertoire.clearAbove
local notation "Xs"=> G hw A
local notation "rX" i:max=> bell M t (a i)
variable (p:∀ i,(P.stampPin t (a i))=(P.vtile t (g i) j)-U i)
variable (q:∀ i,P.stampPin t (w i)=W i)
variable (rA:∀ i,P.BEntry j (w i) (P.shifts j (- (a i-g i j)) (F i)))(E:∀ i,A i=P.HabBox j t (w i) (P.shifts j (- (a i-g i j)) (F i)))
include p
lemma frontal (i:I): (Xs).frontend (fΛ (fun i=>θ i) i) i=(π t (a i):ℝ):=by rw [p i]; rfl
include q
lemma behind (i:I): (Xs).endline (fΛ (fun i=>θ i) i) i=(π t (a i+w i):ℝ):=by unfold Repertoire.endline; rw [frontal _ _ _ _ _ p,minted_val_add,q];rfl

/-- From the left plane: evaluate the entire rope as a single Slabs action,
 acting on the ambient vacuum. Only uses orientation of this axis. Thick mesh. -/
lemma signature (b:ℤ) (L:List I)
    (d:(Xs).Correct L (Repertoire.Pages false) (fΛ (fun i=>θ i)) (some (π t b:ℝ)))
    (r:∀ i,P.BEntry j (w i) (P.shifts j (- (a i - g i j)) (F i)))
    (e:∀ i,A i=P.HabBox j t (w i) (P.shifts j (- (a i-g i j)) (F i))):
    ∃ N:ℕ, P.BEntry j N (χ (-b) (bspin L)) ∧
    (Xs).stageList L (fun i=>θ i) [] (some (π t b:ℝ)) = η (Hβ t N (χ (-b) (bspin L))) Ω:=by
 induction L generalizing b with
 | nil=>
    have q₁:poseTiles P g F []=1:=rfl
    use 1; rw [q₁,map_one]; refine ⟨BEntry.one P j (by decide),?_⟩
    rw [HabBox_one _ P _ (by decide),R.still]; rfl
 | cons i l ih=>
    obtain ⟨d,h⟩:=d
    specialize d (π t b:ℝ) rfl
    have v : (π t b:ℝ) ≤ (π t (a i):ℝ):= (show _≤ (Xs).frontend _ i from d).trans (le_of_eq (frontal R hw t a g p i))
    have h₁: b≤ a i:= (minted_le P t _ _).1 v
    let b':= (a i+w i); let u:ℝ:= (π t b':ℝ); let k:=(a i-b).toNat
    have hk:(k:ℤ)=a i-b:= Int.toNat_of_nonneg (sub_nonneg.mpr h₁)
    have huv:(Xs).endline (fun x=> (((θ i) x).val)) i=u:= behind R hw t a w g p q i
    obtain ⟨N,hN,kN⟩:=ih b' (by rw [behind R hw t a w g p q i] at h; exact h)
    let x:P.Test:= χ (-(a i)) (P.chartAll (g i) (F i))
    let y:= χ (-b') (poseTiles P g F l)
    obtain ⟨e₁,e₂⟩:=R.at_mesh hw (g i) (p i) (q i) (r i) (e i)
    let J:= Hβ t (w i) x; let Z:= Hβ t N y
    have hy: χ (k:ℤ) (x*χ (w i:ℤ) y)= χ (-b) (poseTiles P g F (i::l)):=by
      unfold x y
      change χ _ (_*_)=χ _ (P.chartAll (g i) (F i) * (poseTiles P g F l))
      rw [map_mul,map_mul,P.shifts_sum,P.shifts_sum,P.shifts_sum]
      rw [hk,show a i - b + -a i= -b by omega,show a i - b + (w i:ℤ) + - b'=-b from by unfold b'; omega] -- associativity from order
    have hd:(Xs).sep (some (π t b:ℝ)) i (fΛ (fun i=>θ i) i)=whenly M t k:=by
      change Real.toNNReal ((Xs).frontend _ i-_)=_; rw [frontal R hw t a g p i]
      apply pin_time; rw[hk]; exact minted_sub ..
    use k+(w i+N)
    rw [←hy]; refine ⟨(e₁.concat hN).left k,?_⟩
    rw [Repertoire.stageList,huv]; change (T ((Xs).sep (some _) i (fΛ (fun i=> θ i) i))) (((Xs).visiting (η (A i)) (θ i)) ((Xs).stageList l (fun i=>θ i) [] (some u)))=_
    dsimp only [u]; rw [kN, hd,e₂]
    rw [R.heat,HabBox_left t (e₁.concat hN) k, HabBox_concat t e₁ hN,map_mul,map_mul]; rfl

lemma rankedSalt (L:List I) (d:fΛ (fun i=>θ i)∈ (Xs).planeOK L)
    (r:∀ i,P.BEntry j (w i) (P.shifts j (- (a i - g i j)) (F i)))
    (e:∀ i,A i=P.HabBox j t (w i) (P.shifts j (- (a i-g i j)) (F i))) :
 (Xs).ranking L (fun i=>θ i) []=cost t (poseTiles P g F L):=by
 suffices h:∃ v:ℤ,(Xs).Correct L (Repertoire.Pages false) (fΛ fun i=>θ i) (some ((π t v):ℝ)) ∧
   (Xs).stageList L (fun i=>θ i) [] none=(Xs).stageList L (fun i=>θ i) [] (some ((π t v):ℝ)) by
    obtain ⟨v,d,h⟩:=h
    obtain ⟨N,pN,W⟩:=R.signature hw t a w g p q v L d r e
    unfold Repertoire.ranking; rw [h,W]
    exact (R.expense pN).trans (R.axSym t (-v) (bspin L))
 cases L with
 | nil=> exact ⟨0,trivial,rfl⟩
 | cons i l=>
    have e: ∀ x:ℝ,some ((π t (a i)):ℝ) = some x → (x, (Xs).frontend (fΛ (fun i=>θ i) i) i)∈ Repertoire.Pages false :=by
       intro x p'; rw [← Option.some.inj p',frontal R hw t a g p i]; exact (le_refl (π t (a i):ℝ))
    refine ⟨a i,⟨e,(show _∧_ from (show (Xs).Correct (i::l) (Repertoire.Pages false) _ _ from d)).2⟩,?_⟩
    have h₁:(Xs).sep none i (fΛ (fun i=>θ i) i)=(Xs).sep (some ((π t (a i)):ℝ)) i (fΛ (fun i=>θ i) i):=by
       change 0=((Xs).frontend _ _ - _).toNNReal; rw[frontal R hw t a g p i, sub_self,Real.toNNReal_zero]
    rw [Repertoire.stageList,Repertoire.stageList]; congr 1
    unfold Repertoire.striding; rw [show (Xs).sep _ _ _= _ from h₁]; rfl

omit p q
-- `α` planning arbitrary shared taller. proof NEVER assuming E selection continuous-transverse.
lemma rankedHive {F:I→P.Test}{A:I→P.Slabs j}{g:I → Cover}
 (a:I→ℤ)(w:I→ℕ)(Hw:∀i,π t (a i)=-U i)(v:∀i,π t (w i)=W i)
 (r:∀ i,P.BEntry j (w i) (P.shifts j (- (a i)) (F i)))
 (e:∀ i,A i=P.HabBox j t (w i) (P.shifts j (- (a i)) (F i))) -- hazard A macro
 (L:List I) (d:fΛ (fun i=>P.vtile t (g i))∈ (R.elementals U W hw A).planeOK L):
 (R.elementals U W hw A).ranking L (fun i=>P.vtile t (g i)) []=cost t (poseTiles P g F L):=by
 let b:I→ℤ:=fun i=> a i+g i j
 have h(i:I):b i-g i j=a i:=by unfold b; ring
 exact R.rankedSalt hw t b w g (fun i=> by
    change notch M t (a i+g i j)= notch M t (g i j)-U i
    rw [notch_add, (show notch M t (a i)=-U i from Hw i)]; abel) v L d (fun i=>by rw [h]; exact r i) (fun i=>by rw[h]; exact e i)

variable {t a w g}
lemma rankedMesh {m:I→ℕ} (u:∀ i, P.HabitLevel j (F i) (m i) (-U i) ((-U i)+W i) (A i) t)
    (y:I → Cover)
    (L:List I) (d:fΛ (fun i=>P.vtile t (y i))∈ (Xs).planeOK L):
    (Xs).ranking L (fun i=>P.vtile t (y i)) []=cost t (poseTiles P y (fun i=>P.conveying (m i) (t-m i) (F i)) L):=by
 choose _ a w p q u v using u
 exact R.rankedHive hw _ _ _ p (fun i=> (q i).trans (by abel)) u v L d
lemma fee_hives [Finite I]{m:I→ℕ} (u:∀ i, P.Habitable j (F i) (m i) (-U i) ((-U i)+W i) (A i))
 (x:I→P.VMark)(L:List I)(d:Repertoire.clearAbove (show I→ Axis → marks (timeMesh P.par) from x)∈(Xs).planeOK L): -- macro
 ∀ᶠ t:ℕ in atTop, ∀ y:I → Cover,(∀ i,P.vtile t (y i)=x i) →
  (Xs).ranking L x []=cost t (poseTiles P y (fun i=>P.conveying (m i) (t-m i) (F i)) L):=by
 filter_upwards [eventually_all.mpr (fun i => (u i).event)] with t h y k
 rw [← funext k] at d ⊢; exact R.rankedMesh hw h y L d
end
end Porch
variable {P:Spine}{I:Type}[Fintype I][DecidableEq I]
-- same OPEN plenum results. Inputs may use different heights/axis orders.
variable {cost:ℕ→P.Test→ℂ}{m:I→ℕ}(F:I→P.Test)
variable (C:∀ j:Axis,Porch P cost j)
variable (U W:Axis→I→marks (timeMesh P.par))(hw:∀ j i,0<(W j i:ℝ))
variable (A:∀ j:Axis,I→P.Slabs j)
local notation "X" j:max=> (C j).elementals (U j) (W j) (hw j) (A j)
variable (d:List I)(q:Axis→List I)
variable (p:d.Nodup)(hq:∀ i,d.Perm (q i))
variable (ht:∀ (i:I)(j:Axis),P.Habitable j (F i) (m i) (-(U j i)) (-(U j i)+W j i) (A j i))
-- Mesh and Real cliques for this ordering
noncomputable def prelude : Set (I→Axis→ℝ):=⋂ j:Axis, (X j).highway (q j)
local notation "S◎"=> prelude C U W hw A q
lemma prelude_open : IsOpen (S◎):= isOpen_iInter_of_finite (fun j=>(X j).smooth_highway _)
include hq ht
lemma prelude_plot (j k:Axis):Repertoire.Sharing (X j) (X k) (q j) (q k) (S◎) [] []:=by
 intro x e
 have hv(i:Axis):= Set.mem_iInter.mp e i
 obtain ⟨t,u,v,h⟩:= (((C j).fee_hives (hw j) (fun i=>ht i j) x (q j) ((X j).plane_enough _ (hv j))).and (((C k).fee_hives (hw k) (fun i=>ht i k) x (q k) ((X k).plane_enough _ (hv k))).and (eventually_all.mpr (fun i:I=> mint_voxel (P:=P) (x i))))).exists
 choose y he using h
 apply (u y he).trans; rw [v y he]; apply congrArg
 exact (((hq j).symm.trans (hq k)).map _).prod_eq
include p
lemma prelude_real (j:Axis) (x:I→P.VMark)(e: Repertoire.clearAbove (M:=timeMesh P.par) x∈ S◎) :
 (X j).reading (q j) (Repertoire.clearAbove x)= (X j).ranking (q j) x []:=by
 have h(k : Trans j):=(prelude_plot F C U W hw A d q hq ht j k.val)
 have p:=(hq j).nodup_iff.mp p; rw [(X j).reading_exact]
 exact Repertoire.family_sync (X j) (q j) p (S◎) (prelude_open C U W hw A q)
   (fun k=>⟨(C k.val).H,X (k.val),q k.val,h k⟩) _ _ e
lemma prelude_coast (j k:Axis):Set.EqOn ((X j).reading (q j)) ((X k).reading (q k)) (closure (S◎)):=
 Repertoire.Sharing.smooth (X j) (X k) (q j) (q k) ((hq j).nodup_iff.mp p) ((hq k).nodup_iff.mp p) _
   (prelude_open C U W hw A q) (prelude_plot F C U W hw A d q hq ht j k)
#print axioms prelude_real
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
