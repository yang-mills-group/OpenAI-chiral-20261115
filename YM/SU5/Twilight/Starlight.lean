import YM.SU5.Twilight.Epistle
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open WeakDual TopologicalSpace
open scoped Pointwise
open Lamour Bridge.Celeste Glimpse
open RadiusF Morn Ballad OS ContinuousLinearMap
variable (P: Spine)(j:Axis)(x:P.Spectrum0 j)(s:ℕ)
local notation "K"=> P.calibration
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N₀"=> notch M
local notation "Z₀"=>P.voyageF j x
local notation "v₀" => P.heaven j x
local notation "X"=> P.ColorHil j x
local notation "Y"=>P.physicalEnergy j x
local notation "F"=> P.Viewers j x
local notation "H"=> P.ManyF j x
open OS.Semigroup
lemma stone_norm : ‖P.heaven j x‖=1:= P.norms_color j x
lemma stone_warm (h:P.lodestarHere j x)(a:Cross j) : (P.seasons j x).U a v₀=v₀:= (((P.heavenRank j x h _).1 (Submodule.subset_span (Set.mem_singleton _))).2 a)
lemma stone_mark : P.wealth j x (P.colorZero j x) = P.heaven j x:= Subtype.ext ((Z₀).grounded (look j) (P.leader j x))
lemma bank_orth (a:P.ColorHil j x)(h:inner ℂ (P.colorZero j x) a=0): inner ℂ v₀ (P.wealth j x a)=0:= by
  let k:=P.colorZero j x; let v:=P.visitors j x; change inner ℂ k (v a)=0
  rw [← adjoint_inner_left v,show v.adjoint=v from (Z₀).symmetricstack _ , show v k=k from (Z₀).grounded _ (P.leader j x)]; exact h
lemma bank_cost (a:X): ‖P.wealth j x a‖≤ ‖a‖:=by
 change ‖P.visitors j x a‖ ≤ _; rw [P.visitors_op]; exact (F).norm_starProjection_apply_le a
section analysis
variable {G:Hilbert} {j:Axis}(S:OS.Semigroup G j)
lemma milk (a:ℝ≥0)(x y:G) : inner ℂ x (S.E a y)=inner ℂ (S.E (a/2) x) (S.E (a/2) y):= by nth_rw 1 [←add_halves a]; rw [S.time,ContinuousLinearMap.comp_apply,← adjoint_inner_right,S.sym]
lemma re_milk (a:ℝ≥0)(x:G): (inner ℂ x (S.E a x)).re= ‖S.E (a/2) x‖^2:= by rw [milk]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
lemma milk_toSend (t:Cross j)(a:ℝ≥0)(x:G): ‖inner ℂ x (S.U t (S.E a x))‖≤ (inner ℂ x (S.E a x)).re:=by
 have hv(a:ℝ≥0): S.U t (S.E a x)=S.E a (S.U t x):=DFunLike.congr_fun (S.independent ..).symm x
 rw [hv a,milk,←hv]; apply (norm_inner_le_norm ..).trans_eq; rw [S.unitary,re_milk,sq]
lemma minted (z:Cross j)(x y:G): inner ℂ (S.U z x) (S.U z y)=inner ℂ x y:=
 LinearIsometry.inner_map_map (𝕜:=ℂ) (show G.space →ₗᵢ[ℂ] G.space from { (S.U z).toLinearMap with norm_map':= S.unitary _}) x y
lemma spent (z:Cross j)(x b:G)(r:inner ℂ x b=0)(p:S.U z x=x)(t:‖x‖=1)(a:ℂ):
   (inner ℂ (b+a •x) (S.U z (b+a•x))).re=(inner ℂ b (S.U z b)).re+‖a‖^2:=by
  have h:inner ℂ x (S.U z b)=0:=by nth_rw 1 [←p]; rw [minted,r]
  rw [map_add,map_smul,p,inner_add_right,inner_add_left,inner_add_left,inner_smul_left,h,inner_smul_right (x:=b) (y:=x), ← inner_conj_symm (𝕜:=ℂ) b x,r]; simp only [mul_zero,map_zero,add_zero,zero_add]
  rw [Complex.add_re]; have hu :‖a • x‖=‖a‖:=by rw [norm_smul,t,mul_one]
  congr 1
  exact (inner_self_eq_norm_sq (𝕜:=ℂ) (a • x)).trans (by rw [hu]) -- arguments?
lemma bank_rises (x:G)(z:Cross j) : (inner ℂ x (S.U z x)).re ≤ ‖x‖^2:=(Complex.re_le_norm _).trans ((norm_inner_le_norm ..).trans_eq (by rw [S.unitary,sq]))
lemma polar_land (z a:Cross j)(t:ℝ≥0)(x:G)(e:ℝ)(h:0<e)(p: 4*e < (inner ℂ x (S.U z x)).re)(q:(inner ℂ x (S.U (z+a) x)).re≤ e)(u:(inner ℂ x (S.E t x)).re≤ e) : S.U a (x-S.E t x)≠ x-S.E t x := by
 intro hw; have h0:S.U (z+a) (x-S.E t x)=S.U z (x-S.E t x):= by rw [S.space,ContinuousLinearMap.comp_apply,hw]
 have h':=congrArg (fun y=> (inner ℂ x y).re) h0; simp only [map_sub,inner_sub_right,Complex.sub_re] at h'; have ht(r:Cross j): |(inner ℂ x (S.U r (S.E t x))).re| ≤ e:= (Complex.abs_re_le_norm _).trans ((milk_toSend S r t x).trans u); linarith [abs_le.mp (ht (z+a)),abs_le.mp (ht z)]
end analysis
lemma growsStill (a:X)(z:Cross j)(t:ℝ≥0): let y:= P.wealth j x a; let S:=P.seasons j x; ‖inner ℂ y (S.U z (S.E t y))‖ ≤ (inner ℂ a ((P.physicalEnergy j x).E t a)).re ∧ (inner ℂ y (S.E t y)).re ≤ (inner ℂ a ((P.physicalEnergy j x).E t a)).re:=by
 let v:=P.wealth j x; intro y S; have hv: (inner ℂ y (S.E t y)).re ≤ (inner ℂ a ((P.physicalEnergy j x).E t a)).re:=by
   rw [re_milk,re_milk]; change ‖(P.seasons j x).E (t/2) (P.wealth j x a)‖^2 ≤ _; rw [P.banked j x a, ← P.bankHeat]; exact (pow_le_pow_left₀ (norm_nonneg (v _)) (P.bank_cost ..) 2)
 exact ⟨(milk_toSend S z t y).trans hv,hv⟩

-- Stencil economics into kinetic movement of SMOOTH FIELD
local notation "B"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
variable (z:P.Spectrum0 (3:Axis)) {e c:ℝ}(A:Glimpse.Voyage P.par.block P.calibration.ℓ 4 c (RadiusF.next P.calibration.ℓ))
local notation "S"=> P.seasons (3:Axis) z
local notation "p"=>P.landingP s
local notation "ζ"=> RadiusF.next ℓ
local notation "P⁺" i:max=> P.landingP s+P.driving s i A.port
local notation "A₀"=> P.ColorHil 3 z
local notation "L"=>P.ManyF 3 z
local notation "X₀"=> A.toGaze.hair
variable (i:Trans (3:Axis))(x':Lead.Clan)
local notation "T" u:max=> P.tuneK (Holds (B) (X₀) u)
local notation "φ"=> P.singleState (3:Axis) s z
local notation "W"=> P.wealth (3:Axis) z
local notation "ψ"=> P.heaven 3 z
local notation "f" u:max=> Holds (B) (X₀) u
local notation "χ" a:max=> A.marine.price a
local notation "θ₀"=> A.toGaze.crown
local notation "t₀"=> P.halfTime s A.toGaze.fare
noncomputable def voyager : P.ManyF 3 z := (W) (P.coinK 3 (Holds (B) (X₀) x') z θ₀ s)
noncomputable def moving : P.ManyF 3 z := W (P.centered 3 z (Holds (B) (X₀) x') θ₀ s)
local notation "η"=>P.voyager s z A x'
local notation "σ"=>P.moving s z A x'
local notation "U" x:max=> (S).U x
abbrev funds (e:ℝ):Prop:=∀ q: Company, ‖(φ) (P.tuneK (A.marine.price q))‖ ≤ e
-- project centered with READS nearχ
local notation "z₀"=> (φ) (T x')
lemma near_seen : P.tuneK (χ (Sum.inl (),x'))= P.luggage 3 (look 3) (all0 (ζ)) (T x') * P.reflectTest 3 (T x')-(brill x':ℂ) • (1:P.Test):=by
  rw [P.songsAg _ (pay_A B (ζ) (X₀) x') (by rw [A.concert]; rfl), ← P.travelsT 3 (f x') (look 3) (all0 ζ)]; rfl
lemma distant_seen :
    let t':= P.tuneK (placates_one B X₀ x'); P.tuneK (χ (Sum.inr i,x'))=P.reflectTest 3 t' * P.shifts i.val (A.port:ℤ) (P.luggage 3 (look 3) (all0 ζ) t'):=by
  intro t'
  rw [P.songsAg _ (pay_B B ζ X₀ i A.port x') (by rw [A.concert]; rfl), show t' = _ from (rfl : t'= P.tuneK (placates_one B X₀ x')),← P.travelsT 3 (placates_one B X₀ x')]; rfl
lemma voyagers_agree : η= σ + z₀ • ψ:=by
 unfold voyager; rw [P.coined,map_add,map_smul,P.stone_mark]; rfl
lemma centers_org : inner ℂ ψ σ=0:=P.bank_orth 3 z _ (P.center_value ..)
lemma ashi (h:P.lodestarHere 3 z)(t:Cross 3)(a:ℂ):(inner ℂ (σ+a • ψ) ((U t) (σ+a • ψ))).re=(inner ℂ σ ((U t) σ)).re+‖a‖^2:=spent S t ψ σ (P.centers_org s z A x') (P.stone_warm 3 z h _) (P.stone_norm ..) _
lemma spotlight (h:P.lodestarHere 3 z)(a:P.funds s z A e) : brill x'-e ≤ (inner ℂ σ ((U p) σ)).re + ‖z₀‖^2 :=by
 have ht : ‖inner ℂ η ((U p) η)-(brill x':ℂ)‖ ≤ e:= by
    have hx:= a (Sum.inl (),x'); rw [P.near_seen, map_sub,map_smul,show (φ) 1=1 from ?_, smul_eq_mul,mul_one,← P.near_gram s z (f x') θ₀] at hx; exact hx
    rw [P.single_state,P.reading_unit,map_one]
 rw [P.voyagers_agree] at ht
 have hv:= (Complex.abs_re_le_norm _).trans ht; rw [abs_le,Complex.sub_re, P.ashi s z A x' h, Complex.ofReal_re] at hv; linarith only [hv.1]
lemma shadowed (h:P.lodestarHere 3 z)(a:P.funds s z A e) : (inner ℂ σ ((U (P⁺ i)) σ)).re ≤ e:= by
 let t':=P.tuneK (placates_one B (X₀) x'); let v:=z₀-(purePrice x':ℂ); let r:A₀:=P.coinK 3 (shaded (f x') (purePrice x':ℂ)) z θ₀ s; let Λ:=W r
 have he: W r= σ+v • ψ:=by unfold r; rw [P.songShade («p»:=f x'), map_sub,map_smul,P.stone_mark,show W (P.coinK 3 (f x') z θ₀ s)=η from rfl,P.voyagers_agree, show v=_ from (rfl : v=z₀-(purePrice x':ℂ)),sub_smul]; abel
 have ht: ‖inner ℂ Λ ((U (P⁺ i)) Λ)‖ ≤ e:=by
   have hx:= a (Sum.inr i,x'); rw [show P.tuneK (χ (Sum.inr i,x'))=_ from P.distant_seen A i x',← P.more_gram s z i (placates_one B (X₀) x') θ₀] at hx; exact hx
 have hv:=(Complex.re_le_norm _).trans ht
 change (inner ℂ (W r) ((U (P⁺ i)) (W r))).re ≤ _ at hv
 rw [he,P.ashi s z A x' h] at hv; linarith only [sq_nonneg ‖v‖, hv]
lemma refined_center_heat (β:P.Pulsating z s A.toGaze e): (inner ℂ σ ((S).E t₀ σ)).re ≤ e:= (P.growsStill 3 z _ 0 t₀).2.trans (P.θSingle_x z s A.toGaze x' β)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
