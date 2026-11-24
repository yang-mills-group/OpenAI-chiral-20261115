import GaugeFieldConstruction.RaysMercuryMars
/-!
 # improvement.M Ward-ident at mean. no long-range claim needed.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable {p:Ticket u C}{Y:AreaQc S}
namespace FirstPackMars
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
open Loft
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg



variable (g:SO)(k:Fin n)(F:Fin n→ΧiMars)(x:Points n)(hx:x∈conf n)(b:Bulb)(h:BreatherMars b k x)
variable (p)
abbrev dashMercuryMars (a:SO)(F:Fin n→ΧiMars): Fin n→ΧiMars:= compassPiMars p a ∘ F
variable {p}
lemma dashFillMars (a:SO)(A:ΧiMars):dashMercuryMars p a (Fin.cons A F)=Fin.cons (compassPiMars p a A) (dashMercuryMars p a F):=by ext1 i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
lemma dashChangeMars (a:SO)(A:ΧiMars)(j:Fin n):dashMercuryMars p a (update F j A)=update (dashMercuryMars p a F) j (compassPiMars p a A):=by ext1 i; by_cases h:i=j <;> simp [dashMercuryMars,h]
lemma dashBackMars (a:SO) :dashMercuryMars p a⁻¹ (dashMercuryMars p a F)=F:= inv_inv a ▸ PiFlowCancelMars a⁻¹ F -- tune
lemma dayMotionMars (a:SO)(z:E4): motionMoonMars a (Points.cons z x)= Points.cons (mercuryMars a z) (motionMoonMars a x):=by ext1 i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
include H G h
lemma raysMatchMars (a:Axis)(z:E4)(A:ΧiMars): WheyMars p Y (dashMercuryMars p g⁻¹ F) (motionMoonMars g⁻¹ x) (FlameMoonMars b g) a A z=∑ i:Axis,g.val.val i a • WheyMars p Y F x b i (compassPiMars p g A) (mercuryMars g z) :=by
 let W:= motionMoonMars g⁻¹ x; let J:=dashMercuryMars p g⁻¹ F
 let C:=mercuryMars g z; let M:=TerraMars (n:=n+1) p Y; let Q:= M (Fin.cons (compassPiMars p g A) F) (Points.cons C x)
 change D _ _ _ • M _ _=_; rw [show (∑ i:Axis,g.val.val i a • WheyMars p Y F x b i (compassPiMars p g A) (mercuryMars g z)) = (D (basis a) (FlameMoonMars b g).f z) • Q from ?_]
 · by_cases u:D (basis a) (FlameMoonMars b g).f z=0
   · rw[u, zero_smul,zero_smul]
   let B:=FlameMoonMars b g
   have ht:Points.cons z W∈conf (n+1):=RoomMars _ _ _ (sparkTiltMars g k x b h) _ (cone B a (subset_tsupport _ (show (LED B a).f z≠0 from u)))
   have he:=VitaPiiotMars H G g _ (Fin.cons A J) _ ht
   change M (dashMercuryMars p g _) (motionMoonMars g (Points.cons z W))=_ at he
   rw [dayMotionMars, dashFillMars,show dashMercuryMars p g J=F from PiFlowCancelMars ..,show motionMoonMars g W=x from ?_] at he
   exact congrArg ((D (basis a) B.f z) • ·) he.symm
   unfold W; simpa using LunarwayMars g⁻¹ x
 rw [burnRateMars,Finset.sum_smul]; apply sum_congr rfl; intro i _; exact (smul_assoc (_:ℝ) (D _ b.f C) Q).symm
lemma flagMatchMars (a:Axis)(A:ΧiMars): FlossMars p Y (dashMercuryMars p g⁻¹ F) (motionMoonMars g⁻¹ x) (FlameMoonMars b g) a A=∑ i:Axis,g.val.val i a • FlossMars p Y F x b i (compassPiMars p g A):=by
 unfold FlossMars; simp_rw [raysMatchMars H G g k F x b h]
 let N:= mercuryMars g; have V:= N.measurePreserving; let K: Homeomorph E4 E4:= N.toHomeomorph
 have hr (i:Axis):= WheyCanMars p Y k F x b h i (compassPiMars p g A)
 have hi (i:Axis): Integrable (fun z:E4=>g.val.val i a • WheyMars p Y F x b i (compassPiMars p g A) (mercuryMars g z)):= (V.integrable_comp_of_integrable (hr i)).smul (g.val.val i a)
 rw[integral_finsetSum _ fun i _=>hi i]; apply sum_congr rfl; intro i _; rw[integral_smul,(V.integral_comp K.measurableEmbedding (WheyMars p Y F x b i _))]
lemma rentShiftMars (j:Axis): Analysis.D (direction k j) (TerraMars p Y F) x=∑ a:Axis,FlossMars p Y F x b a (unitsMars p g a j):=by
 let W:= motionMoonMars g⁻¹ x; let J:=dashMercuryMars p g⁻¹ F; let C:= compassPiMars p g
 rw [OrbitTrackMars H G g⁻¹ k F x h.bounds]; change (∑ a:Axis,(_ : ℝ) • D (direction k a) (TerraMars p Y J) W)=_
 have he:= sparkTiltMars g k x b h; -- at motion
 simp_rw [PoemMoonMars p Y k J W (FlameMoonMars b g) he, Finset.smul_sum]
 have v(c i a:Axis): FlossMars p Y J W (FlameMoonMars b g) c (p.J i a)=∑ k':Axis, g.val.val k' c • FlossMars p Y F x b k' (C (p.J i a)):= flagMatchMars H G g k F x b h c _
 let z (a c s:Axis):= grainRayMars g.val j a • g.val.val s c • FlossMars p Y F x b s (C (p.J c a))
 simp_rw[v,Finset.smul_sum]; change (∑ a:Axis,∑ c:Axis,∑ s:Axis,z a c s)=_
 rw[show (∑ a:Axis,∑ c:Axis,∑ s:Axis,z a c s)=(∑ s:Axis,∑ c:Axis,∑ a:Axis,z a c s) from ?_]; swap
 · rw [Finset.sum_comm, Finset.sum_comm (s:=Finset.univ) (f:=fun s c=>∑ a:Axis,z a c s)]; apply sum_congr rfl; intro i _; exact Finset.sum_comm
 apply sum_congr rfl; intro s _
 let u:= FlintMars p Y F x b k h s; change _= u (∑ a:Axis,∑ b:Axis,(parcelMars g.val s a*parcelMars g.val j b) • C (p.J a b)); simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro i _; unfold z; rw[smul_smul,mul_comm,← Complex.ofReal_mul]; exact Complex.real_smul .. -- tune
omit H G h
lemma sumFrameRateMars {B:Type*}[NormedAddCommGroup B][NormedSpace ℝ B][CompleteSpace B](Y:Axis→ΧiMars→ₗ[ℝ] B)(k:Axis)(v:B)(u:∀ g:SO,∑ a:Axis,Y a (unitsMars p g a k)=v): ∑ a:Axis,Y a (TotalStarsMars p a k)=v:=by
 let Z(a b:Axis):ΧiMars→ₗ[ℝ] B:= if b=k then Y a else 0
 have he(x:SumMoonMars)(a):∑ b:Axis,Z a b (x a b)=Y a (x a k):=by
    rw [sum_eq_single k]
    · simp [Z]
    · intro b _ h; simp [Z,h]
    simp
 have h:=totalRateMars p Z v (fun g=>by simp_rw[he]; exact u g); simp_rw [he] at h; exact h
include H G h
lemma OrbitFluxMars (j:Axis): Analysis.D (direction k j) (TerraMars p Y F) x=∑ a:Axis,FlossMars p Y F x b a (TotalStarsMars p a j):= by
 symm; exact sumFrameRateMars (fun a=>(FlintMars p Y F x b k h a).restrictScalars ℝ) j _ (fun s=>(rentShiftMars H G s k F x b h j).symm)
omit h H G
noncomputable def ColumnMoonMars (p:Ticket u C)(Y:AreaQc S)(k:Fin n)(x:Points n)(hx:x∈conf n)(F:Fin n→ΧiMars)(a:Axis):ΧiMars→ₗ[ℂ]ℂ:= (cloakMMars p Y x hx ([direction k a])).toLinearMap F k
lemma columnBillMars (A:ΧiMars) i:ColumnMoonMars p Y k x hx F i A=Analysis.D (direction k i) (TerraMars p Y (update F k A)) x:=rfl
include H G hx
lemma stationMarksMars (j:Axis): (∑ a:Axis,D (direction k a) (TerraMars p Y (update F k (unitsMars p g a j))) x)=0:=by
 simp_rw [← columnBillMars k F x hx] -- tune
 let Va:=compassPiMars p g; let U(a:Axis):=ColumnMoonMars p Y k x hx F a
 change (∑ a:Axis,U a (unitsMars p g a j))=_
 let F':=dashMercuryMars p g⁻¹ F; let W:= motionMoonMars g⁻¹ x
 have he (b c: Axis) : D (direction k b) (TerraMars p Y (update F' k (p.J b c))) W= ∑ a:Axis,parcelMars g.val a b * (U a (Va (p.J b c))):=by
    rw [OrbitTrackMars H G g k _ W (NSF.Points.move_in _ hx)]
    rw [show motionMoonMars g W=x from by unfold W; simpa using LunarwayMars g⁻¹ x, show (compassPiMars p g) ∘ (update F' k (p.J b c))=update F k (Va (p.J b c)) from ?_]; exact sum_congr rfl fun i _=> Complex.real_smul ..
    exact (dashChangeMars _ _ _ _).trans (congrArg (fun f':Fin n→ΧiMars=>update f' k _) (show dashMercuryMars p g F'=F from PiFlowCancelMars g F)) -- tune
 unfold unitsMars TensPitchMars pileMoonMars; simp_rw [map_sum,map_smul]
 let Z(a b c:Axis):= parcelMars g.val j c * (parcelMars g.val a b * U a (Va (p.J b c)))
 have ξ : ∀ a b c:Axis,(parcelMars g.val a b*parcelMars g.val j c) • (U a (compassPiMars p g (p.J b c))) = Z a b c:= fun a b c=> by rw[smul_eq_mul]; dsimp only [Z,Va]; ring
 simp_rw [ξ]
 rw [show (∑ a:Axis,∑ b:Axis,∑ c:Axis,Z a b c)=(∑ c:Axis,∑ b:Axis,∑ a:Axis,Z a b c) from ?_]
 · apply sum_eq_zero; intro c _; unfold Z; simp_rw [← mul_sum, ← he]; unfold W; rw [divMars p Y k F' c _ (NSF.Points.move_in _ hx),mul_zero]
 rw [Finset.sum_comm, Finset.sum_comm (s:=Finset.univ) (f:=fun c b=>∑ a:Axis,Z a b c)]; apply sum_congr rfl; intro i _; exact Finset.sum_comm
lemma TotalDivergenceMars (j:Axis): ∑ a:Axis,D (direction k a) (TerraMars p Y (update F k (TotalStarsMars p a j))) x=0:= sumFrameRateMars (fun a=>(ColumnMoonMars p Y k x hx F a).restrictScalars ℝ) j _ (fun g=>stationMarksMars H G g k F x hx j)
#print axioms OrbitFluxMars
#print axioms TotalDivergenceMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
