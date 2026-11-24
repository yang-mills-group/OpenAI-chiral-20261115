import YM.SU5.SatinWard.Resolution.Monaco
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal

open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
open Motet SoulField Verdance Mezzo SatinWard.Installment
namespace Imperial

/- Lining incidence, with E estimator small-step. Keep exactly compressed-prices
 in this stage. (Adjoint tests have separate qualification through actual lease.) -/
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} (q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)(k:Axis)(t:Fin 8)
local notation "ρ" => P.par.block.val
local notation "κ" => ζ -- macro
local notation "LH"=> liner k t
local notation "Yt" b:max=> castY t b
local notation "So" t:max=> CLine q k t
local notation "Y" v:max=> home P (So t) v
local notation "Zt" b:max v:max=> home P (So (Yt b)) v
local notation "Pt" t:max=> lifeC q p k t
local notation "p*t"=> lifeC q p k t -- tokens
variable (U:Soul)(vo:Axis)
local notation "VBar" i:max z:max => JpriceApp P (So i) M (Pt i) z vo v
local notation "Top" b:max=> (VBar (Yt b) U)
local notation "UV" z:max=> cloakF P M (Pt t) (substar (v:=v) (j:=ρ) P vo k z) v
local notation "Εw" k:max => Motet.dewy P.par k
local notation "Ε" k:max=> (↑(Εw k):ℂ)
local notation "UR" b:max=> (P.chartAll (liner k t b) (VBar (Yt b) U).F)
variable {s:ℕ} (i:Axis)(x:P.Spectrum0 i)(hp:f0 ≤ v){l r:ℝ}
local notation "tₖ" i:max u:max => P.tock v ((u:Cover) i)
local notation "Q₀"=> home P (So t) v i
local notation "𝔤"=> P.Grips i x v (-(l-Q₀)) (r+Q₀)
local notation "ℛ"=>P.charter i x
local notation "Σ★"=> P.locate i x
local notation "Hσ" A:max => (fun l r=> P.rawBase i x A (l-home P (So t) v i) (r+home P (So t) v i))
local notation "𝒵" b:max => galley P i x v (liner k t b) (Hσ (Top b)) l r
local notation "δ₀"=>moonClock P s
variable {o: Cover}(uv:StretchClock P P.par.block.val s v (CLine q k t) o)
variable (W:HeartClock P f0 H A a b φ P.par.block.val M D η)(ht7:f0 ≤ s)
variable (hl:2*moonClock P s ≤ l)(hr:2*moonClock P s≤ r)
variable (K:P.NightCop)(lι:Wage3){U':Soul}{D':ℕ→ℕ} (Hχ: Velas P η A H f0 v P.par.block.val vo k lι U D')(Hd:Tendsto D' atTop atTop)
-- MotionLap on those projected transfers
local notation "Kℓ" => ShapeLab.leg lι
local notation "Φv" u:max=> annoFace P i x v (Y v) (VBar t u)
local notation "Φℓ" b:max=> Beam P q k t v b
local notation "φ🌸" z:max=> (fun (t:Fin 8)=> annoFace P i x v (home P (So t) v) (VBar t z))
local notation "γb" b:max z:max=> bead P q k t i x v (φ🌸 z) l r b
local notation "μ" => sprintCost P.par.R.L
local notation "Ψε" b:max => bondMonth P η A s b
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i) : NormedSpace ℝ (P.ManyF i x).Op:= opRn (P.ManyF i x)
variable (c:s<v) (pT:Tendsto D atTop atTop)(e:Melodic P η A f0 D) (R:Resonant P η A H f0 P.par.block.val)[Nonempty η] {a₁ b₁ φ' :ℝ}(Wa:HeartClock P f0 H A a₁ b₁ φ' P.jump128 M D η)
local notation "Z₀" i:max=> trueKey P pT e K i
local notation "Ψ𝓡" b:max=> (priceX P pT e vo (So b) M K (Pt b) i x)
local notation "Φ" z:max => fun b:Fin 8=> priceX P pT e vo (So b) M K (lifeC q p k b) i x z
local notation "βQ" b:max z:max=> bead P q k t i x v (Φ z) l r b
local notation "δη" z:max=> spindle P q k t i x v (Φ z) l r -- clock frontier
noncomputable def noteLens (v:ℕ)(h:f0≤v)(j a:Axis)(i:Wage3):Soul:=(R.shop v h j a i D pT).choose_spec.2.choose
local notation "DΦ" v:max h:max=> noteLens P η pT R v h vo k
include pT in
lemma givenM (h:f0≤v): ∃ Z:ℕ→ℕ, StrictMono Z∧ Velas P η A H f0 v (ρ) vo k lι ((DΦ v h) lι) (D ∘ Z):=by
 have h':=R.shop v h vo k lι D pT; exact ⟨h'.choose,h'.choose_spec.1,h'.choose_spec.2.choose_spec⟩
-- limiter map N' with argument X applied after normalization (`μ same sale`). η factor `dewy`. Lap minus two included later.
noncomputable def frameDiadem (v:ℕ)(i j:Axis): Soul→ₗ[ℝ] Soul := if h:f0 ≤ v then ShapeLab.columns (noteLens P η pT R v h i j) else 0
local notation "MF" s:max=> frameDiadem P η pT R s vo k
local notation "με" s:max=> (Motet.dewy P.par s)⁻¹
noncomputable def poleLens (v:ℕ)(a v':Axis): Soul→ₗ[ℝ] Soul:= ((με v) • (Z₀ v).symm.toLinearEquiv.toLinearMap).comp (frameDiadem P η pT R v a v') |>.comp (Z₀ v).toLinearEquiv.toLinearMap
-- order. use `include .. R`? implicitly P W proof. H input not inferred? poleLens signature uses section η and H even though via R; lean prints.
local notation "NF" t:max=> poleLens P η K pT e R t vo k
lemma authδ (v:ℕ) (z:Soul) : (NF v) z=(με v) • (Z₀ v).symm ((MF v) ((Z₀ v) z)):=rfl -- syntax `(Z₀ v) z`
local notation "ZQ" t:max => P.locate i x t -- t not fixed
noncomputable abbrev climber (t: Vantage): (P.ManyF i x).Op →ₗ[ℝ] (P.ManyF i x).Op:= ({ toFun := P.locate i x t, map_add' := P.locate_add i x t, map_smul' a b:= P.locate_smul i x t b a }: (P.ManyF i x).Op→ₗ[ℂ](P.ManyF i x).Op).restrictScalars ℝ
include W Wa ht7 hl hr K c pT e
lemma jewel_diadem (κ':ℝ)(pF:f0≤v)(kq: dayNum P η s v vo A H ≤ κ') : ‖δη U-(Ψ𝓡 t) ((NF v) U) l r‖ ≤ (Fintype.card Wage3:ℝ)*(κ'*‖((Z₀ v) U)‖):=by
 have u0:=clockP P s; let Hu(b:Bool):=adjacentP P η q p M k t i W ht7 hl hr c.le b; let tχ(b:Bool):=(climber P i x (Φℓ b)).comp (contoBill P pT e vo _ M K (Pt (Yt b)) i x W (u0.trans_le (Hu b).1) (u0.trans_le (Hu b).2))
 let t0:=contoBill P pT e vo _ M K (Pt t) i x W (by linarith only [u0,hl]:0<l) (by linarith only [u0,hr]:0<r); let j:= tχ true+tχ false-t0.comp (NF v); let F':=j.comp (Z₀ v).symm.toLinearEquiv.toLinearMap
 change ‖j U‖≤_; rw [show j U= F' ((Z₀ v) U) from (by change j U=j ((Z₀ v).symm ((Z₀ v) U)); rw [(Z₀ v).symm_apply_apply]),←columns_map (M:=F')]; refine columns_price _ _ _ (fun w=>?_)
 let z:=(Z₀ v).symm (ShapeLab.leg w); change ‖(δη z)-(Ψ𝓡 t) ((NF v) z) l r‖ ≤ _
 rw [authδ, show (Z₀ v) z=ShapeLab.leg w from (Z₀ v).apply_symm_apply _, frameDiadem,dif_pos pF,columns_one]
 obtain ⟨D,h,Dh⟩:=givenM P η k vo w pT R pF; exact (trail P η q p M k t _ vo i x W ht7 hl hr K w Dh (pT.comp h.tendsto_atTop) c pT e Wa).trans kq
omit ht7 hl hr c
include R
local notation "Quota"=> (julyP P)
local notation "AX" s:max => (σ s)^(15/8:ℝ)
lemma crown_year : ∃ E:ℝ, E>0∧∀ (v s:ℕ),f0 ≤ s→ s<v→∀ (q: Cover)(p:ResidualPermit q) (j:Axis)(x:P.Spectrum0 j)(ti:Axis)(t:Fin 8)(u:Soul)(l r:ℝ),2*moonClock P s ≤ l→ 2*moonClock P s≤ r→
 let Q(t:Fin 8):= priceX P pT e vo (CLine q ti t) M K (lifeC q p ti t) j x; let m:= poleLens P η K pT e R v vo ti; ‖spindle P q ti t j x v (fun a:Fin 8=>Q a u) l r- Q t (m u) l r‖ ≤ E* μ^s *(AX v)*‖u‖:=by
 obtain ⟨T,h,hK⟩:= wire_num P η M vo Wa; obtain ⟨D',q,hq⟩:= fiscal_meter P η M Wa; let t0:=P.macroStep 0
 let w₀:=t0^(15/8:ℝ); have ht:0<w₀:=Real.rpow_pos_of_pos (P.macroStep_pos _) _
 let KΓ:= (Fintype.card Wage3:ℝ); let c:=KΓ*T; have hp:0<c:=mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (zero_lt_one.trans_le h) -- Nonempty Wage3 maybe only from using instance. need `count_pos_J` token
 refine ⟨c*D'/w₀,by positivity,fun v s p' k q p j x i t z l r hl hr=>?_⟩; intro W' m
 let ι':= Ω★; let w:=(Εw v)⁻¹*((μ^(v-s))⁻¹); let Xv:=(unitX P)^v
 have e':0<w:=mul_pos (inv_pos.mpr (intLive _)) (inv_pos.mpr (pow_pos (sprint_pos _) _)); have z':‖(Z₀ v) z‖≤ Xv*‖z‖:= κgrow P _ pT e K z (p'.trans_lt k) -- argument order
 let wμ:= lapQ P.run s; let hT:= hK v s p'; have hS:T*wμ*((Motet.dewy P.par v)⁻¹)*(μ^(v-s))⁻¹=T*wμ*w:=by unfold w; ring
 rw [hS] at hT; have u:= (W.tally.date.stock _ p').1; have th:=le_trans hT (c:=T*w) ((mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (zero_le_one.trans h) u.2) e'.le));
 let h':= jewel_diadem P η q p M i t z vo j x W p' hl hr K k pT e R Wa _ (p'.trans k.le) th
 refine h'.trans ?_; change KΓ*(T*w* ‖((Z₀ v) z)‖)≤ _; rw [monad_eq P]; have he:=have i:=hq _ _ k.le; (show Xv*w≤ D'*μ^s*Quota⁻¹^v from (by rw [show Xv*w=Xv*((Motet.dewy P.par v)⁻¹)*(μ^(v-s))⁻¹ from (by unfold w; ring)]; exact i))
 let ν:= μ^s*Quota⁻¹^v; change _ ≤ c*D'/w₀*μ^s*(w₀*(Quota⁻¹)^v)*‖z‖
 calc
    _ ≤ KΓ*(T*w*(Xv*‖z‖)):=by gcongr
    _ = c*(Xv*w)*‖z‖:=by unfold c; ring
    _ ≤ c*(D'*μ^s * (Quota⁻¹)^v)*‖z‖:=by gcongr
    _ = _:=by field [ht.ne'] -- ht shadow
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
