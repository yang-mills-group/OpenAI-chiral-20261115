import YM.SU5.Assay.WickOut
import YM.SU5.Assay.SeenBox
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
/-! Even if enjoying some cost not explicitly enclosing the component terms
 separately: cancel sticker price whenever the question lies in Cinder.
 In particular under re-presentation into a very short cost. -/
local notation "μ"=> P.meanBox j
local notation "Π"=> (P.Hil j).space
local notation "Mₒ"=> (P.Hil j).Op
local notation "ω"=> P.euclOp j

private lemma dyad {a:ℝ≥0}{x:Π}(h:ω (a+a) x=0):ω a x=0:=by
  let T:=ω a
  have p:T.adjoint= T:=advance_adjoint ..
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  have w:T.adjoint (T x)=0:=by rw [p];rw [euclOp,advance_smag] at h;exact h
  rw [show inner ℂ (T x) (T x)=inner ℂ x (T.adjoint (T x)) by rw [ContinuousLinearMap.adjoint_inner_right],w,inner_zero_right]
private lemma only_void {a:ℝ≥0}{x:Π}(h:ω a x=0):x=0:=by
 let f(n:ℕ):ℝ≥0:=a*(2⁻¹)^n
 have g(n):ω (f n) x=0:=by
    induction n with
    | zero=>simpa [f]
    | succ n ih=>
      apply dyad
      rw [show f (n+1)+f (n+1)=f n from by unfold f; rw [pow_succ,←mul_assoc]; rw [←div_eq_mul_inv, add_halves]]
      exact ih
 have gone:Tendsto f atTop (𝓝 0):=by
    have e:Tendsto (fun n:ℕ=>((2:ℝ≥0)⁻¹)^n) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one zero_le (by norm_num)
    simpa [f] using e.const_mul a
 let y:=advance_strong Y H V (π).circuit j 0 false C₀ x
 have d:= (y.continuous.tendsto 0).comp gone
 change Tendsto (fun n=>ω (f n) x) atTop (𝓝 (ω 0 x)) at d
 have p:ω 0 x=0:= tendsto_nhds_unique (d.congr g) tendsto_const_nhds
 rwa [euclOp,advance_source, ContinuousLinearMap.id_apply] at p
private lemma debt_left {T:Mₒ}{a:ℝ≥0}(p:ω a*T=0):T=0:=ContinuousLinearMap.ext fun x=> only_void (DFunLike.congr_fun p x : ω a (T x)=0)
private lemma debt {T:Mₒ}{a c:ℝ≥0}(p:ω a*T*ω c=0):T=0:=by
 have h:=congrArg star (debt_left ((mul_assoc ..).symm.trans p))
 rw [star_mul,star_zero,show star (ω c)=ω c from advance_adjoint ..] at h
 exact star_eq_zero.mp (debt_left h)
variable (P) in
def Cinder:Submodule ℂ P.Test:=Submodule.span ℂ {x:P.Test|P.GFlame x}

/-- Asking 0-price with sticker left end at `-n`, for span induction. -/
private def Washed (P:Spine)(j:Axis)(s n:ℕ)(f:P.Test):Prop:=
 ∃ w:ℕ,P.BEntry j w (P.shifts j n f)∧ P.meanBox j s w (P.shifts j n f)=0
variable (s)
private lemma cinder_pads (R:P.Register)(h:f∈ P.Cinder):∀ᶠ n in atTop,P.Washed j s n f:=by
 apply Submodule.span_induction (p:=fun f _=> ∀ᶠ n in atTop,P.Washed j s n f) _ _ _ _ h
 · intro x e
   obtain ⟨S,u⟩:= findsBay K x
   filter_upwards [P.eventually_BFits S,eventually_ge_atTop 1] with n p z
   have t:=p.admit u n j le_rfl (v:=n+n) (by omega) (by omega)
   exact ⟨_,t,GFlame.operator s t (GFlame.shift e _ _) R⟩
 · apply Eventually.of_forall;intro n;unfold Washed;rw [map_zero]
   exact ⟨1,BEntry.zero P j one_pos, meanBox_zero s _ _ one_pos⟩
 · intro x y _ _ t q
   filter_upwards [t,q] with n ⟨a,u,v⟩ ⟨c,k,l⟩
   let ua:=u.right (Nat.le_add_right a c)
   let kc:=k.right (Nat.le_add_left c a) -- signature
   unfold Washed; rw [map_add]
   refine ⟨a+c,ua.add kc,?_⟩
   rw [meanBox_add s ua kc,meanBox_right s u c,v,zero_mul,Nat.add_comm a c,meanBox_right s k a,l,zero_mul,add_zero]
 intro a x _ t
 filter_upwards [t] with n ⟨c,k,l⟩
 unfold Washed; rw [map_smul]
 exact ⟨_,k.smul a,(meanBox_smul s k a).trans (by rw [l,smul_zero])⟩

lemma Cinder.operator (R:P.Register)(h:f∈ P.Cinder): μ s w f=0:=by
 by_cases p:P.BEntry j w f
 swap; · unfold meanBox;rw [dif_neg p]
 obtain ⟨n,a,g,y⟩:=(cinder_pads (j:=j) s R h).exists
 have t:=meanBox_pad s p n a
 apply debt (t.symm.trans ?_)
 rw [Nat.add_comm _ a,meanBox_right s g,y,zero_mul]

lemma Cinder.charge (v:P.GFlame f):f∈P.Cinder:= Submodule.subset_span v
lemma Cinder.value (h:f∈P.Cinder)(x:P.Spectrum0 j):P.singleState j s x f=0:=by
 exact Submodule.span_induction (p:=fun f _=> P.singleState j s x f=0) (fun f v=>GFlame.value v ..) (by rw [map_zero]) (fun a c _ _ y z=>by rw [map_add,y,z,add_zero]) (fun a y _ z=>by rw [map_smul,z,smul_zero]) h
lemma Cinder.shift (h:f∈P.Cinder)(j:Axis)(a:ℤ):(P.shifts j a f)∈P.Cinder:=by
 exact Submodule.span_induction (p:=fun f _=> P.shifts j a f∈P.Cinder) (fun _ u=>Cinder.charge (GFlame.shift u _ _)) (by rw [map_zero];exact P.Cinder.zero_mem) (fun _ _ _ _ g k=>by rw [map_add];exact P.Cinder.add_mem g k) (fun z _ _ g=> by rw [map_smul]; exact P.Cinder.smul_mem z g) h

variable (w)
lemma Cinder.room (R:P.Register)(h:f∈P.Cinder)(x:P.Spectrum0 j):
  (P.doorBox j s w f).1.1= P.meanBox j s w f ∧ P.seenBox j x s w f=0∧P.singleState j s x f=0:=by
 have p:=Cinder.operator s (j:=j) (w:=w) R h
 have d:P.doorBox j s w f=0:=by
   by_cases t:P.BEntry j w f∧ f∈enclave K
   · exact Subtype.ext (Subtype.ext ((doorBox_val s t.1 t.2).trans p))
   unfold doorBox;rw [dif_neg t]
 constructor
 · rw [d,p];rfl
 unfold seenBox; rw[d,map_zero];exact ⟨rfl,Cinder.value s h x⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
