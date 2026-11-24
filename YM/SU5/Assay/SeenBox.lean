import YM.SU5.Assay.BEntry
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

/-! The operator with calipers in forward ticks; default 0 is immaterial.
 `meanBox`: primary Hilbert before vacuum selection.
 `doorBox`: restricted to physical marks & lives in physical slab algebra.
 `seenBox`: represented in selected Hilbert (prior to transversely continuous part). -/

variable (P j) (x:P.Spectrum0 j)
noncomputable def meanBox (s w:ℕ)(f:P.Test): (P.Hil j).Op:=
 if h:P.BEntry j w f then P.Box j s w h.pos (h.card s) else 0
local notation "A₀"=>P.Physical j
local notation "Φ"=>P.colorSpace j x
noncomputable def doorBox (s w:ℕ)(f:P.Test):P.Physical j:=
 if h:P.BEntry j w f ∧ f∈enclave K then P.door j s w h.1.pos (h.1.card s) h.2 else 0
noncomputable def seenBox (s w:ℕ)(f:P.Test): (P.ColorHil j x).Op:=
 Φ (P.doorBox j s w f)

local notation "μ"=> P.meanBox j
local notation "Β"=> P.seenBox j x
local notation "δ"=>P.doorBox j
local notation "E"=> P.euclOp j
local notation "W"=> (P.physicalEnergy j x).E
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.colorZero j x
local notation "T"=> enclave P.calibration
private lemma dig (a c:A₀) : a.1.1=c.1.1 → a=c :=fun h=>Subtype.ext (Subtype.ext h)

variable {P j}(s)
lemma meanBox_card (F:P.Card j s w)(h:0<w)(t:P.entryTest j s F=f): μ s w f=P.Box j s w h F:=by
 have u:=BEntry.ofCard F h t
 unfold meanBox; rw [dif_pos u,u.agrees t]
lemma meanBox_eq (h:P.BEntry j w f): μ s w f=P.Box j s w h.pos (h.card s):=
   meanBox_card s (h.card s) h.pos rfl
lemma doorBox_val (h:P.BEntry j w f)(t:f∈T): (P.doorBox j s w f).1.1=P.meanBox j s w f:=by
 unfold doorBox meanBox; rw [dif_pos h,dif_pos (And.intro h t)]; rfl
lemma seenBox_card (F:P.Card j s w)(h:0<w)(e:P.entryTest j s F∈T)(t:P.entryTest j s F=f):
    Β s w f=Φ (P.door j s w h F e):=by
 have u:=BEntry.ofCard F h t; apply congrArg Φ; apply dig
 rw [doorBox_val s u (t ▸ e)]
 exact meanBox_card s F h t
lemma seenBox_pay (h:P.BEntry j w f)(e:f∈T): ‖Β s w f‖≤ ‖μ s w f‖:=by
 rw [←doorBox_val s h e]
 exact NonUnitalStarAlgHom.norm_apply_le Φ _
lemma seenBox_scalar (h:P.BEntry j w f)(e:f∈T): inner ℂ Ω (Β s w f Ω)= P.singleState j s x f:=by
 rw [seenBox_card s x (h.card s) h.pos e (f:=f) (by exact Subtype.ext rfl),P.attended,P.view_scalar]; rfl
lemma singleState_le_meanBox (h:P.BEntry j w f)(e:f∈T): ‖P.singleState j s x f‖ ≤ ‖μ s w f‖:=by
 have hu:‖Ω‖=1:=origin_norm _ (P.unit_too j x)
 rw [←seenBox_scalar s x h e]
 apply (norm_inner_le_norm ..).trans
 rw [hu,one_mul]
 exact ((Β s w f).le_opNorm Ω).trans (by rw [hu,mul_one]; exact seenBox_pay s x h e)

lemma meanBox_unit (P:Spine)(j:Axis)(p:0<w): P.meanBox j s w 1 =P.euclOp j (whenly (timeMesh P.par) s w):=
 (meanBox_card s (SlabMark.identity P.run P.large s j false w) p rfl).trans (ticket_birth ..)
lemma meanBox_zero (P:Spine)(j:Axis)(p:0<w):P.meanBox j s w 0=0:=by
 have h:= BEntry.zero P j p; exact (meanBox_eq s h).trans (P.box_zero j s w p _ rfl)
lemma meanBox_lin (p:P.BEntry j w f)(q:P.BEntry j w g)(z:ℂ):
 μ s w (z•f+g)=z•μ s w f+ μ s w g:=by
 rw [meanBox_eq _ ((p.smul z).add q),meanBox_eq s p,meanBox_eq s q]; exact P.box_linear _ _ _ _ _ _ _ _ rfl
lemma meanBox_add (p:P.BEntry j w f)(q:P.BEntry j w g):μ s w (f+g)=μ s w f+μ s w g:=by
 simpa using meanBox_lin s p q 1
lemma meanBox_smul (p:P.BEntry j w f)(z:ℂ):μ s w (z•f)=z•μ s w f:=by
 simpa [meanBox_zero _ _ _ p.pos] using meanBox_lin s p (BEntry.zero P j p.pos) z
lemma meanBox_sub (p:P.BEntry j w f)(q:P.BEntry j w g):μ s w (f-g)=μ s w f-μ s w g:=by
 simpa [sub_eq_add_neg,meanBox_smul _ q] using (meanBox_add s p (q.smul (-1)) |>.trans <|
  congrArg (fun u=> μ s w f+u) (meanBox_smul s q (-1)))

lemma meanBox_concat (p:P.BEntry j w f)(q:P.BEntry j v g): μ s (w+v) (f*σ w g)= μ s w f * μ s v g:=by
 rw [meanBox_eq s p,meanBox_eq s q]
 exact (meanBox_card s (edit Y H s j false w v (p.card s) (q.card s)) (add_pos p.pos q.pos) (Subtype.ext (editor ..))).trans (edit_comp ..).symm
lemma meanBox_raise (p:P.BEntry j w f)(t:ℕ)(h:s≤t): μ t (L^(t-s)*w) (P.conveying s (t-s) f)= μ s w f:=by
 rw [meanBox_eq s p]
 exact (meanBox_card t (furnished Y H s π j false w (p.card s) t h) (p.raise s t h).pos rfl).trans (refined_box ..).symm
lemma meanBox_right (p:P.BEntry j w f)(n:ℕ): μ s (w+n) f= μ s w f * E (Ν s n):=by
 rw [meanBox_eq s (p.right (Nat.le_add_right w n)),meanBox_eq s p]
 exact shape_right Y H V s π Qt j false C₀ w w (p.card s) p.pos n _ rfl
lemma meanBox_left (p:P.BEntry j w f)(n:ℕ): μ s (n+w) (σ n f) = E (Ν s n) * μ s w f:=by
 rw [meanBox_eq s (p.left n), meanBox_eq s p]
 exact shape_left Y H V s π Qt j false C₀ w w (p.card s) p.pos n _ rfl
lemma meanBox_pad (p:P.BEntry j w f)(n m:ℕ): μ s (n+w+m) (σ n f) = E (Ν s n) * μ s w f * E (Ν s m):=by
 rw [meanBox_right s (p.left n),meanBox_left s p]

lemma norm_pads_mul {X:Type*} [NormedRing X] (l a r:X)(hx:‖l‖≤1)(hy:‖r‖≤1): ‖l*a*r‖ ≤ ‖a‖:=by
 
 refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hy).trans ?_)
 exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) hx)
lemma meanBox_pad_le (p:P.BEntry j w f)(n m:ℕ): ‖μ s (n+w+m) (σ n f)‖ ≤ ‖μ s w f‖:=by
 rw [meanBox_pad s p]
 exact norm_pads_mul _ _ _ (P.heat_norm j _) (P.heat_norm j _)

lemma seenBox_zero (p:0<w): Β s w 0=0:=by
 have d: δ s w 0=0:=by
   apply dig; rw [doorBox_val s (BEntry.zero _ _ p) (zero_mem _)]
   exact meanBox_zero s _ _ p
 unfold seenBox; rw [d,map_zero]
lemma seenBox_add (p:P.BEntry j w f)(q:P.BEntry j w g)(e:f∈T)(t:g∈T):Β s w (f+g)= Β s w f+Β s w g:=by
 unfold seenBox; refine Eq.trans (congrArg Φ ?_) ((Φ).toAlgHom.map_add (δ s w f) (δ s w g)); apply dig
 change _= (δ s w f).1.1+(δ s w g).1.1
 rw [doorBox_val s p e,doorBox_val s q t,doorBox_val s (p.add q) ((T).add_mem e t)]
 exact meanBox_add s p q
lemma seenBox_smul (p:P.BEntry j w f)(e:f∈T)(a:ℂ):Β s w (a•f)=a•Β s w f:=by
 unfold seenBox; refine Eq.trans (congrArg Φ ?_) ((Φ).toAlgHom.toLinearMap.map_smul a (δ s w f)); apply dig
 change _=a•(δ s w f).1.1
 rw [doorBox_val s p e,doorBox_val s (p.smul a) ((T).smul_mem e a)]
 exact meanBox_smul s p a
lemma seenBox_sub (p:P.BEntry j w f)(q:P.BEntry j w g)(e:f∈T)(t:g∈T):Β s w (f-g)= Β s w f-Β s w g:=by
 unfold seenBox; rw [←map_sub]; apply congrArg Φ; apply dig
 change _= (δ s w f).1.1-(δ s w g).1.1
 rw [doorBox_val s p e,doorBox_val s q t,doorBox_val s (p.sub q) ((T).sub_mem e t)]
 exact meanBox_sub s p q
lemma seenBox_sum {I:Type*}(p:0<w)(d:Finset I)(f:I→P.Test)(h:∀i∈d,P.BEntry j w (f i))(e:∀i∈d,f i∈T):
 Β s w (∑i∈d,f i)=∑i∈d,Β s w (f i):=by
 induction d using Finset.induction with
 | empty=> simp only [Finset.sum_empty,seenBox_zero _ _ p]
 | insert i d t ih=>
   have u:=mem_insert_self i d; have z : ∀i∈d,P.BEntry j w (f i):=fun k hk=>h k (mem_insert_of_mem hk)
   have q : ∀i∈d,f i∈T:=fun k hk=>e k (mem_insert_of_mem hk)
   rw [sum_insert t,sum_insert t,seenBox_add _ _ (h i u) (BEntry.sum p d f z) (e i u) ((T).sum_mem q),ih z q]
lemma seenBox_raise (p:P.BEntry j w f)(e:f∈T)(t:ℕ)(h:s≤t): Β t (L^(t-s)*w) (P.conveying s (t-s) f)= Β s w f:=by
 unfold seenBox; apply congrArg Φ; apply dig
 rw [doorBox_val s p e,doorBox_val t (p.raise s t h) (P.refine_keeps _ _ e _)]
 exact meanBox_raise s p t h
lemma seenBox_pad (p:P.BEntry j w f)(e:f∈T)(n m:ℕ): Β s (n+w+m) (σ n f) = W (Ν s n)* Β s w f * W (Ν s m):=by
 change Φ _=Φ (P.risesColor _ _) * Φ _* Φ (P.risesColor _ _)
 rw [←map_mul,←map_mul]
 apply congrArg Φ; apply dig
 change _= E _ * (δ s w f).1.1 * E _
 rw [doorBox_val s p e,doorBox_val s (p.pad n m) (P.shifts_keep j _ e)]
 exact meanBox_pad s p n m
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
