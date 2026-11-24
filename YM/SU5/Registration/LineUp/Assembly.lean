/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.LineUp.OrderEcho
import YM.SU5.Registration.Sectors.Polity
import YM.Fields.Spectrum
/-!
 # Construct Symmetries on this sector from the Eu price, buys cone (115-style upgrade over this axis) here
 Conditional. Keeps B. Doesn't claim operator commutation yet.
 adapts YM/Fields/Motion & Spectrum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Filter MeasureTheory Measure Set Complex Submodule SatinRegistration
open Boundary Probe Mink Mink.Poincare OS OS.Semigroup SatinEdge.RealSheet Analysis
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{S: _root_.YM.OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
variable (B:Carton S V) (J:JMap V)(R:Courts V)(F:InkWaves V)(W:WView V)(U:InkPort B F W)
variable (z:Remembers B J)(u:R.Carriage F) (m:R.Parley J)
local notation "Φ" => B.citizen
local notation "K"=> B.pointShelf
local notation "L"=> B.station
abbrev seedPorts:= Finsupp.linearCombination ℂ B.engaged
lemma seed_ports_noted (v:MarkWords V) : B.seedPorts (Finsupp.single v 1)=B.engaged v:= by simp only [seedPorts,Finsupp.linearCombination_single,one_smul]
lemma owns_stems : LinearMap.range B.seedPorts= B.citizen:= Finsupp.range_linearCombination ..
lemma tickets : DenseRange B.seedPorts:= by change Dense (LinearMap.range B.seedPorts:Set L); rw [B.owns_stems]; exact B.populous
lemma bud_hit {A B' : (L).Op} (h:∀ i,A (B.engaged i)= B' (B.engaged i)) : A=B':=by
 have ht (x : MarkWords V →₀ ℂ) : A (B.seedPorts x)=B' (B.seedPorts x) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,hf,hg]
    | single a r => simp only [seedPorts,Finsupp.linearCombination_single,map_smul,h]
 exact DFunLike.coe_injective (B.tickets.equalizer A.continuous B'.continuous (funext ht))
-- general word selection
lemma beam (q:MarkWords V→ L) (p:∀ x y, inner ℂ (q x) (q y)=inner ℂ (B.engaged x) (B.engaged y)) : ∃ U : B.station.Op, (∀ i,U (B.engaged i)=q i) ∧ ∀ v : B.station,
    ‖U v‖=‖v‖ := by
 let F := Finsupp.linearCombination ℂ q
 have he (x y : MarkWords V →₀ ℂ) : inner ℂ (F x) (F y) = inner ℂ (B.seedPorts x) (B.seedPorts y) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add q v hP hQ => simp only [map_add,inner_add_left,hP,hQ]
    | single i a =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add q v hP hQ => simp only [map_add,inner_add_right,hP,hQ]
      | single j b => simp only [F,seedPorts,Finsupp.linearCombination_single, inner_smul_left,inner_smul_right,p]
 have hp x : ‖F x‖=‖B.seedPorts x‖ := by
    nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [he, ← @norm_eq_sqrt_re_inner ℂ]
 let U:= F.extendOfNorm B.seedPorts; have ht x: U (B.seedPorts x)=F x:= LinearMap.extendOfNorm_eq B.tickets ⟨1,fun i=>by simp [hp]⟩ _
 exact ⟨U,fun i=> by nth_rw 1 [← B.seed_ports_noted i]; rw [ht]; simp [F], fun i => congr_fun (B.tickets.equalizer U.continuous.norm continuous_norm (funext fun j => (congr_arg _ <| ht j).trans (hp j))) i⟩

private lemma strong_life (Y : Poincare → B.station.Op) (h : ∀ p,∀ v : B.station, ‖Y p v‖=‖v‖) (hp : ∀ i, Continuous fun p => Y p (B.engaged i)) :
    ∀ v : B.station,Continuous fun p => Y p v := by
  have he (i : MarkWords V →₀ ℂ) : Continuous fun p => Y p (B.seedPorts i) := by
    induction i using Finsupp.induction_linear with
    | zero => simp; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single i b => simp_rw [seedPorts,Finsupp.linearCombination_single,map_smul]; exact (hp i).const_smul b
  intro v; apply continuous_iff_continuousAt.mpr; intro p
  apply Metric.tendsto_nhds.mpr; intro ε hε
  obtain ⟨_,⟨i,rfl⟩,hi⟩ := Metric.mem_closure_iff.mp (B.tickets v) (ε/3) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (he i|>.tendsto p) (ε/3) (by positivity)] with u hu
  have hU k : dist (Y k v) (Y k (B.seedPorts i))=dist v (B.seedPorts i) := by rw [dist_eq_norm,dist_eq_norm, ← map_sub,h]
  apply lt_of_le_of_lt (dist_triangle _ (Y u (B.seedPorts i)) _)
  have ht := dist_triangle (Y u (B.seedPorts i)) (Y p (B.seedPorts i)) (Y p v)
  rw [dist_comm (Y p (B.seedPorts i)) (Y p v),hU] at ht
  rw [hU]; linarith

def Joins (A:Action B.station):Prop:=∀ i p,A.V p (B.engaged i) = B.engaged (R.exchanges p i)
variable (A: Boundary.Action B.station) (j:B.Joins R A)
include U z u m
lemma unites : ∃ A:Boundary.Action B.station, B.Joins R A:=by
 have hp (p q:MarkWords V): inner ℂ (B.engaged p) (B.engaged q)=W.kernel J p q:= (B.literal_gram J F W U z p q).symm -- trim args
 have hx(x y : MarkWords V)(p:Poincare) : inner ℂ (B.engaged (R.exchanges p x)) (B.engaged (R.exchanges p y))=inner ℂ (B.engaged x) (B.engaged y):=by simp only [hp]; exact R.color_like U u J m p x y
 choose Vg hv w using fun p => B.beam (B.engaged ∘ R.exchanges p) (fun x y=> hx x y p)
 have he p i : Vg p (B.engaged i)= B.engaged (R.exchanges p i) := hv p i
 let A : Action B.station:= { V := Vg
                              one := B.bud_hit fun i=> by rw [he,R.passport_pt]; rfl
                              mult := fun p q=> B.bud_hit fun i=> by rw [ContinuousLinearMap.comp_apply,he,he,he,R.passport_comp]
                              usual:=w
                              strong := strong_life B Vg w fun i=> by
                                simp_rw [he]; apply continuous_iff_continuousAt.mpr; intro p; apply OS.ketC _ (D:=L)
                                · simp_rw [hx]; exact continuousAt_const
                                simp_rw [hp]; exact (R.chambers_word W J _ _).continuousAt }
 exact ⟨A,fun i p=>he p i⟩
omit U z u m
include j
lemma unanimous_time : A.orbit=B.joinT:=by
 have he(x:E4): A.orbit.translation x=B.joinT.translation x:=by
    refine bud_hit B (fun i=> ?_); change A.V _ _=_; rw [j,B.along_t]; suffices h:R.foreign (translation x)=euSlide (V:=V) x by unfold Courts.exchanges; rw [h]
    exact funext fun p=> R.foreign_slide x p
 exact (show ∀ x y:Spectral.Orbit B.station E4,x.translation=y.translation→x=y from fun x y h=>by cases x; cases y; congr) _ _ (funext he)
lemma real_pvm : A.orbit.Spectrum B.joinT.P:=by rw [unanimous_time B R A j]; exact B.joinT.total
lemma real_cone : B.joinT.P.region Mink.coneᶜ=0:=by
 -- PVM order uses spectral char scalar all v. use Action.south
 rw [← B.unanimous_time R A j]; refine A.south (fun v=>?_)
 rw [Boundary.Action.μ,B.unanimous_time R A j,B.sees_m]; exact S.nonneg v.val
lemma district (p:Poincare) : MapsTo (A.V p) B.citizen B.citizen := by
 intro x hx; change x∈B.citizen at hx; rw [← B.owns_stems] at hx; obtain ⟨a,rfl⟩:=hx; change A.V p _∈ B.citizen
 induction a using Finsupp.induction_linear with
 | zero=> rw [map_zero,map_zero]; exact (Φ).zero_mem
 | add x y h t=> rw [map_add,map_add]; exact (Φ).add_mem h t
 | single i c=> rw [seedPorts,Finsupp.linearCombination_single,map_smul,j]; exact (Φ).smul_mem _ (B.evaluate _).prop
noncomputable def liftV (p:Poincare): B.citizen →ₗ[ℂ] B.citizen:=
 (A.V p).toLinearMap.restrict (p:=B.citizen) (q:=B.citizen) (B.district R A j p)
lemma liftV_trans (p:Poincare)(v: Φ) : (B.liftV R A j p v).1 = A.V p v.val:=rfl
lemma walks (p:Poincare)(v:MarkWords V) : B.liftV R A j p (B.evaluate v)= B.evaluate (R.exchanges p v):=Subtype.ext (j ..)
omit j in
lemma buds_pt {X:Type*}[AddCommGroup X][Module ℂ X](U V':Φ→ₗ[ℂ] X) (p:∀ i,U (B.evaluate i)=V' (B.evaluate i)): U=V':=by
 let F':= Finsupp.linearCombination ℂ B.evaluate
 have ht(v:Φ): v ∈ LinearMap.range F':=by
    have hp:v.val∈ LinearMap.range B.seedPorts:= (le_of_eq B.owns_stems.symm v.prop) -- notation greek
    obtain ⟨y,k⟩:=hp; refine ⟨y,Subtype.ext (?_)⟩; rw [← k]; -- proof subtype ext orientation, typeclass diamonds
    change (Φ).subtype _=_; have ht: (Φ).subtype.comp F'= B.seedPorts:= by
       apply LinearMap.ext; intro f; induction f using Finsupp.induction_linear with
       | zero=> simp
       | add i t h u=> simp only [map_add,h,u]
       | single i c=> simp only [LinearMap.comp_apply,F',seedPorts,Finsupp.linearCombination_single,map_smul]; rfl
    exact LinearMap.congr_fun ht y
 ext1 i; obtain ⟨x,rfl⟩:= ht i; induction x using Finsupp.induction_linear with
 | zero=> simp
 | add i j h t=> simp only [map_add,h,t]
 | single i c=>simp only [F',Finsupp.linearCombination_single,map_smul,p]
lemma agnostic (p:Poincare)(x:V)(f:Test4) (q: B.citizen) : A.V p (B.pointMap x f q).1=(B.pointMap (R.mi p.Λ x) (Joint.push p f) (B.liftV R A j p q)).1:= by
 let U:= B.liftV R A j p
 have hx: U.comp (B.pointMap x f)=(B.pointMap (R.mi p.Λ x) (Joint.push p f)).comp U:= by
    refine buds_pt B _ _ (fun i=>?_); simp only [LinearMap.comp_apply,← B.eval,U, B.walks]; rfl
 exact congrArg Subtype.val (LinearMap.congr_fun hx q)
lemma fields_covariant (p:Poincare)(x:V)(f:Test4): (B.liftV R A j p).comp (B.pointMap x f)=(B.pointMap (R.mi p.Λ x) (Joint.push p f)).comp (B.liftV R A j p):=LinearMap.ext (fun q=> Subtype.ext (agnostic B R A j p x f q)) -- maybe defeq
lemma feet (p:Poincare) : A.V p (B.evaluate []).1=(B.evaluate []).1:= j [] p
lemma ahead_price (x:E4)(p:B.citizen): B.liftV R A j (translation x) p=B.exportTime x p:=by
 apply Subtype.ext; rw [B.passport]; change A.orbit.translation x p.val=_; rw [unanimous_time B R A j]
end YM.SatinWFixed.Carton
open YM.SatinWFixed.Carton
#print axioms unites
#print axioms agnostic
#print axioms real_cone
#print axioms liftV_trans
