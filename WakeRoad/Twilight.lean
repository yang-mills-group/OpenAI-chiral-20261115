import WakeRoad.Title
import WakeRoad.Tackle
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
open Dial Pressure
open Stationary (Gaia)
set_option quotPrecheck false
open Onyx
variable {E:ℝ}{Mc n:ℕ}{P:Spine}{K:P.Register} {r f:ℕ→ℕ}
local notation "Y"=>P.run
local notation "Λ"=>P.par
local notation "iA" n:max=> P.period (P.projection.rows (f n))
local notation "kA" n:max=> P.cutoff (P.projection.columns (f n))
local notation "ν" s:max n:max=> side Y (iA n) s
local notation "Gξ" s:max n:max=> (Λ).V.L.H ((Y).uv (kA n)-s)
local notation "rξ" s:max n:max=> flatSea Y s (iA n) (kA n)
variable (Q: Spine.PreparedInvestment P K E Mc)
-- rescaled measurements
section spin
variable (G:ℕ→ Fin n→ Staff)(L:Fin n→ Ballad.Twah.DirSpin)
local notation "filmSpin" sn:max i:max => alleyHue (G (sn:ℕ×ℕ).1) (ν sn.1 sn.2) (rξ sn.1 sn.2) i
variable (u:StrictMono f)(hp:Tendsto r atTop atTop)(hr:∀ i,0<r i)(Z: Fin n→ Gaia) (h:∀ i j,
    Tendsto (fun s=>riseX (r s) ((G s i).u-(G s j).u)) atTop (𝓝 (Z i-Z j)))(b:∀ i j,Z i=Z j→∀ᶠ s:ℕ in atTop,(G s i).u=(G s j).u) (e:∀ s i,(G s i).spin=L i)
include Q u hp hr h b e
lemma spinLens (i:swatches n): Tendsto (fun sn:ℕ×ℕ=>(r sn.1:ℂ)^(3*n)*filmSpin sn i) stairs (𝓝 (Hearth.schedule i Z L)) :=by
 obtain ⟨v,T⟩:= Q.investment; let X:= fun s i=>(G s i).u; intro S pS; rw [Filter.mem_map]; apply eventually_curry_iff.mpr
 filter_upwards [title (n:=n) Y P.law P.history T Q.dispatch Q.rocky.merit (I:=1) (by norm_num),amble L X r hp h b (Λ).K.j (nontrivial_spin Λ) hr i S pS] with s p h'
 filter_upwards [u.tendsto_atTop.eventually p,(steps_sides P f u s).eventually h'] with m q w
 change (_*Hearth.pigment _ _ 1 _ _ _ _) ∈ S; rw [show (fun i=>(G s i).spin)= L from funext (e s)]; exact w q.2.1 _ _ (preparedFlat ..)

omit Q u hp hr h b e in
lemma prism_nonzero : (Fintype.card SU.group.ColorIndex:ℂ)≠0:=by
 haveI:Nontrivial SU.group.Color:=Thera.yet_one.nontrivial_color
 have ht:0<SU.group.lieDim:=by rw [Gauge.lieDim,←SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
 change (Fintype.card (Fin SU.group.lieDim):ℂ)≠0; rw [Fintype.card_fin]; exact_mod_cast ht.ne'
variable (F:Fin n→ PlaqAxes)
variable (hF:∀ s i,(G s i).face.2=F i)(z:∀ i j,Tendsto (fun s=> riseX (2*(r s:ℝ)) ((G s i).face.1-(G s j).face.1)) atTop (𝓝 (Z i-Z j)))
abbrev beamCoin (s:Side)(i j: Staff)(c d:SU.group.ColorIndex)(M:Bed):ℂ:=coupon (Staff.localFace i s) (Staff.localFace j s) c d M
abbrev hardCoin (Z:Fin n→Gaia)(D:Fin n→PlaqAxes)(i j:Fin n)(c d:SU.group.ColorIndex):ℂ := (sch (G:=SU.group) c d:ℂ)* Regis.Circuit.specter (D i) (D j) (Z i-Z j)
include hF z
omit Q h b e
lemma Beam_poll(i j:Fin n)(k:Z i≠Z j)(c d:SU.group.ColorIndex): Tendsto (fun sn:ℕ×ℕ=>((2*(r sn.1:ℝ):ℝ):ℂ)^4*beamCoin (ν sn.1 sn.2) (G sn.1 i) (G sn.1 j) c d (Gξ sn.1 sn.2)) stairs (𝓝 (hardCoin Z F i j c d)):=by
 let X:=fun s=> G s i; let W:=fun s=> G s j; let I:ℂ:= Fintype.card SU.group.ColorIndex; let K:ℂ:= (↑(sch (G:=SU.group) c d))/I
 have ht(I':ℂ): K*(I*I')=(sch (G:=SU.group) c d:ℂ)*I':=by rw [←mul_assoc, show K*I=_ from div_mul_cancel₀ _ prism_nonzero]
 have he:= (gauge_target (P:=P) hr hp X W (sub_ne_zero.mpr k) (z i j) u (F i) (F j) (fun s=> hF s i) (fun s=>hF s j)).const_mul K
 unfold speckleV acePower at he; rw [ht] at he; refine he.congr fun x=>?_; unfold gaugeCoupon beamCoin coupon; let v:=ν x.1 x.2; change K * ((_:ℂ)^4 * (I * _))= _; rw [mul_left_comm K,ht]
end spin
set_option maxHeartbeats 300000
variable {β:ℕ→ℝ}(HM:Pooling P.run (P.period∘P.projection.rows) (P.cutoff∘ P.projection.columns) f β)

local notation "rock" s:max m:max=> reachCost Y s (iA m) (kA m) (κFix β s)
def tideSeat (G:ℕ→Fin n → Staff)(sn:ℕ×ℕ):ℂ:= seatT Y sn.1 (iA sn.2) (kA sn.2) (propel (G sn.1) (ν sn.1 sn.2)) (Hearth.brush (alleyHue (G sn.1) (ν sn.1 sn.2) (rξ sn.1 sn.2))) (κFix β sn.1)

include HM
lemma tideCost : Tendsto (fun sn:ℕ×ℕ=>((rock sn.1 sn.2:ℝ):ℂ)) stairs (𝓝 1) := by
 suffices h : Tendsto (fun sn:ℕ×ℕ=> (rock sn.1 sn.2:ℝ)) stairs (𝓝 1) by simpa only [comp_def,Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp h
 refine Metric.tendsto_nhds.mpr fun ε p=> ?_; rw [eventually_curry_iff]; exact Eventually.of_forall fun s=> Metric.tendsto_nhds.mp (Gathering P.run HM s) ε p
section two
variable (hp:Tendsto r atTop atTop)(hr:∀ i,0<r i)
variable (G:ℕ→Fin 2 → Staff)(L:Fin 2→Ballad.Twah.DirSpin)(F: Fin 2→ PlaqAxes)(O:Fin 2→ Gaia)(j:∀ i j,Tendsto (fun s=>riseX (r s) ((G s i).u-(G s j).u)) atTop (𝓝 (O i-O j))) (z:∀ i j,Tendsto (fun s=> riseX (2*(r s:ℝ)) ((G s i).face.1-(G s j).face.1)) atTop (𝓝 (O i-O j))) (h:∀ s i,(G s i).face.2=F i)(H:∀ s i,(G s i).spin=L i)(p:Injective O)
include Q hp hr j z h H p
abbrev duoTarget(O:Fin 2→Gaia)(L: Fin 2→ Twah.DirSpin)(F:Fin 2→ PlaqAxes):=∑ i:swatches 2,hardCoin O F (0:Fin 2) 1 (i 0) (i 1)*Hearth.schedule i O L
lemma DuoRank : Tendsto (fun sn:ℕ×ℕ=> staffWeight (r sn.1)^2*tideSeat (P:=P) (f:=f) (β:=β) G sn) stairs (𝓝 (duoTarget O L F)):= by
 let X (a:Fin 2)(i:ℕ):=G i a
 let K (v:ℕ×ℕ)(c:swatches 2):ℂ:= ((2*(r v.1:ℝ):ℝ):ℂ)^4 * beamCoin (ν v.1 v.2) (X 0 v.1) (X 1 v.1) (c 0) (c 1) (Gξ v.1 v.2)
 have hb(i:swatches 2): Tendsto (fun x=> K x i) stairs (𝓝 (hardCoin O F 0 1 (i 0) (i 1))):= Beam_poll (P:=P) G HM.up hp hr O F h z 0 1 (p.ne (by decide)) _ _
 let T'(v:ℕ×ℕ)(i:swatches 2):ℂ:= (r v.1:ℂ)^(3*2) * alleyHue (G v.1) (ν v.1 v.2) (rξ v.1 v.2) i
 have he(i:swatches 2):Tendsto (fun v:ℕ×ℕ=> K v i*T' v i) stairs (𝓝 (hardCoin O F (0:Fin 2) 1 (i 0) (i 1)*Hearth.schedule i O L)):= (hb i).mul (spinLens Q G L HM.up hp hr O j (fun i a v=>Eventually.of_forall (fun s=>congrArg (fun i=>(G s i).u) (p v))) H i)
 have ht:=((tideCost HM).pow 2).mul (tendsto_finsetSum (univ:Finset (swatches 2)) (fun i _=> he i)); rw [one_pow,one_mul] at ht
 refine ht.congr fun x=>?_
 let b:=x.2; let s:=x.1; let K':=(Λ).V.L; let d:= (Y).uv (kA b) - s; let U:swatches 2→ℂ:= alleyHue (G s) (ν s b) (rξ s b)
 let J:= K'.roof d; let a:= rock s b; let Q':=ν s b
 have hc:tideSeat (P:=P) (f:=f) (β:=β) G x= (a:ℂ)^2* ∑ c:swatches 2, beamCoin Q' (X 0 s) (X 1 s) (c 0) (c 1) (K'.H d)*U c:=steer_two (K'.mood d) (K'.tied d) (G s) U a (J.2.1 _) J.1 (Λ).K.width
 change _ * (∑ i, K x i * T' x i)=_
 rw [hc,mul_sum,mul_sum,mul_sum]; refine sum_congr rfl fun i _=>?_ ; change _=((staffWeight (r x.1))^2 * (_*(beamCoin _ _ _ _ _ _ * _)))
 unfold K T' staffWeight U a; change ((rock x.1 x.2:ℝ):ℂ)^2*((((2*(r x.1:ℝ):ℝ):ℂ)^4 * beamCoin Q' (X 0 s) (X 1 s) (i 0) (i 1) (K'.H d))* ((r x.1:ℂ)^(3*2) * alleyHue (G s) Q' (rξ s b) i))=((r x.1:ℂ)^3*((↑(2*(r x.1:ℝ)):ℂ)^2))^2*((((rock x.1 x.2:ℝ):ℂ)^2)*(beamCoin Q' (X 0 s) (X 1 s) (i 0) (i 1) (K'.H d) * alleyHue (G s) Q' (rξ s b) i)); ring
end two
section four
variable (hp:Tendsto r atTop atTop)(hr:∀ i,0<r i)
variable (G:ℕ→Fin 4 → Staff)(L:Fin 4→Ballad.Twah.DirSpin)(F: Fin 4→ PlaqAxes)(O:Fin 4→ Gaia)(j:∀ i j,Tendsto (fun s=>riseX (r s) ((G s i).u-(G s j).u)) atTop (𝓝 (O i-O j))) (z:∀ i j,Tendsto (fun s=> riseX (2*(r s:ℝ)) ((G s i).face.1-(G s j).face.1)) atTop (𝓝 (O i-O j))) (h:∀ s i,(G s i).face.2=F i)(H:∀ s i,(G s i).spin=L i)(p:Injective O)
include Q hp hr j z h H p
abbrev galaTarget(O:Fin 4→Gaia)(L: Fin 4→ Twah.DirSpin)(F:Fin 4→ PlaqAxes):=∑ i:swatches 4,wickTranche (fun a b=>hardCoin O F a b (i a) (i b))*Hearth.schedule i O L
lemma GalaRank : Tendsto (fun sn:ℕ×ℕ=> staffWeight (r sn.1)^4*tideSeat (P:=P) (f:=f) (β:=β) G sn) stairs (𝓝 (galaTarget O L F)):= by
 let X (a:Fin 4)(i:ℕ):=G i a
 let K (v:ℕ×ℕ)(c:swatches 4)(a b:Fin 4):ℂ:= ((2*(r v.1:ℝ):ℝ):ℂ)^4 * beamCoin (ν v.1 v.2) (X a v.1) (X b v.1) (c a) (c b) (Gξ v.1 v.2)
 let N'(i:swatches 4)(a b:Fin 4):=hardCoin O F a b (i a) (i b)
 have hb(i:swatches 4)(a b:Fin 4)(d:a≠b): Tendsto (fun x=> K x i a b) stairs (𝓝 (N' i a b)):= Beam_poll (P:=P) G HM.up hp hr O F h z a b (p.ne d) _ _
 let T'(v:ℕ×ℕ)(i:swatches 4):ℂ:= (r v.1:ℂ)^(3*4) * alleyHue (G v.1) (ν v.1 v.2) (rξ v.1 v.2) i
 have he(i:swatches 4):Tendsto (fun v:ℕ×ℕ=> wickTranche (K v i)*T' v i) stairs (𝓝 (wickTranche (N' i)*Hearth.schedule i O L)):=
   (show Tendsto (fun v:ℕ×ℕ=> wickTranche (K v i)) stairs (𝓝 (wickTranche (N' i))) from ((((hb i 0 1 (by decide)).mul (hb i 2 3 (by decide))).add ((hb i 0 2 (by decide)).mul (hb i 1 3 (by decide)))).add ((hb i 0 3 (by decide)).mul (hb i 1 2 (by decide))))).mul (spinLens Q G L HM.up hp hr O j (fun i a v=>Eventually.of_forall (fun s=>congrArg (fun i=>(G s i).u) (p v))) H i)
 have ht:=((tideCost HM).pow 4).mul (tendsto_finsetSum (univ:Finset (swatches 4)) (fun i _=> he i)); rw [one_pow,one_mul] at ht
 refine ht.congr fun x=>?_
 let b:=x.2; let s:=x.1; let K':=(Λ).V.L; let d:= (Y).uv (kA b) - s; let U:swatches 4→ℂ:= alleyHue (G s) (ν s b) (rξ s b)
 let J:= K'.roof d; let a:= rock s b; let Q':=ν s b; let ψ(c:swatches 4)(i j:Fin 4):=beamCoin Q' (X i s) (X j s) (c i) (c j) (K'.H d)
 have hc:tideSeat (P:=P) (f:=f) (β:=β) G x= (a:ℂ)^4* ∑ c:swatches 4, wickTranche (ψ c)*U c:=steer_four (K'.mood d) (K'.tied d) (G s) a U (J.2.1 _) J.1 (Λ).K.width
 change _ * (∑ i, wickTranche (K x i) * T' x i)=_
 rw [hc,mul_sum,mul_sum,mul_sum]; refine sum_congr rfl fun i _=>?_
 let φ:ℂ:= (↑(2*(r s:ℝ)):ℂ); have hx : K x i=fun a b=> (φ^2)^2*ψ i a b:= by rw [show (φ^2)^2=φ^4 by ring]
 rw [hx,dry_clock (φ^2)]; unfold staffWeight
 change (a:ℂ)^4*((φ^2)^4*wickTranche (ψ i) * ((r s:ℂ)^(3*4)*U i))=((r s:ℂ)^3*φ^2)^4*((a:ℂ)^4*(wickTranche (ψ i)*U i))
 ring
end four
#print axioms DuoRank
#print axioms GalaRank
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
