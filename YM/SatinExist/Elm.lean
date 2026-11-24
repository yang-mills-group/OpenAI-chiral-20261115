import YM.SatinExist.Elder
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 370000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
variable (P:Spine)(x:P.Spectrum0 3)(c r:ℕ→ℕ)(Z:Lead.Clan)
local notation "M"=>timeMesh P.par
local notation "X"=>P.ColorHil 3 (P.advocate 3 x 3)
local notation "ℰ" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "E"=> (ℰ).E
local notation "V"=>P.advocate 3 x 3
local notation "E!" s:max i:max=> whenly (timeMesh P.par) s i
local notation "q'" n:max=> P.probeClock n 3
variable (Y:P.Apron)
#check when_le
#check matchR
lemma stitchEd {s n:ℕ}(p:Y.s ≤ s)(t:(q' n) < Y.zoom P s 3):
    let L:= P.thinMat Z s n; let B:= P.stitchApron Z Y s n; let z:=Y.zoom P s 3
    B.engine P 3 (P.advocate 3 x 3)= E (E! s (B.u 3))* (Y.engine P 3 V) * P.swordA 3 V L (E! s (z-L.u 3)) (E! s z):=by
 intro L B z; let h:= L.u (3:Axis); let d:= z-h; let w:= B.u 3
 have hp:0<w:=B.pos 3; have ht:h<z:=t; have he:0<d:=by unfold d; omega
 have hv:0 < h:=L.pos 3; have hx:0 < z:=by omega
 let A:= Y.engine P 3 V; let A':= L.engine P 3 V; let E0:= E (E! s w);
 let S':=(P.shifts 3 z (Y.full P s)); let T':= P.shifts 3 h ((P.thinMat Z s n).F)
 have h1:= P.cashOne 3 V (n:=s) hp
 have h2:P.PrismS 3 V s (z+z) (add_pos hx hx) S' (A):= P.meterRule 3 V Y p
 have h3:=P.cashOne 3 V (n:=s) he; have h4:P.PrismS 3 V s (h+h) (add_pos hv hv) T' A':= P.meterRule0 3 V _; have h5:=P.cashOne 3 V (n:=s) hx
 have h6:= P.cashMul 3 V h4 h5
 have hY:= P.cashMul 3 V (P.cashMul 3 V h1 h2) (P.cashMul 3 V h3 h6)
 simp only [one_mul,P.shifts_sum,map_one,mul_one,map_mul] at hY
 have hT:w=z+3*z+h:=rfl
 have eq:P.shifts 3 w B.F=P.shifts 3 (w:ℤ) S' * _:= (map_mul (P.shifts 3 (w:ℤ)) S' _)
 rw [P.shifts_sum] at eq
 let Q:=P.swordA 3 V L (E! s d) (E! s z)
 change _= E (E! s w) * A * Q
 refine P.values_too 3 V s (w+w) (add_pos hp hp) (P.meterRule0 3 V B) ?_
 unfold T' at hY; rw [P.shifts_sum] at hY; rw [eq];
 have hx':((w+(z+z):ℕ):ℤ)+d + h= (w:ℤ)+ P.fusionFare Y s:=by change _= (w:ℤ)+(↑(3*z):ℤ); unfold d; omega
 rw [P.shifts_sum]; rw [P.shifts_sum,hx'] at hY
 have ht'{v u:ℕ}{p_:0<v}{x0:P.Test}{A B:(X).Op}(h:P.PrismS 3 V s v p_ x0 A)(a:v=u)(t:0<u)(b:A=B): P.PrismS 3 V s u t x0 B:=by subst v B; exact h
 exact ht' hY (by unfold d; omega) _ (by unfold Q swordA; simp only [mul_assoc]; try rfl
 )
local notation "Q" i:max=> E! (c i) (q' (r i))
local notation "Y₀" s:max n:max=> P.stitchApron Z Y s n
-- for n(c i), r i
abbrev zt(Y:P.Apron):= whenly (timeMesh P.par) Y.s (Y.u 3)
-- approximation heats LARGE panel, not requiring thought ratio
lemma sword_moves (U:LargeM P c r) (B: StrictMono c) :
    Tendsto (fun i=> (Y₀ (c i) (r i)).engine P 3 V - E (E! (c i) ((Y₀ (c i) (r i)).u 3))* (Y.engine P 3 V) * (demerit Z • E (P.zt Y+P.zt Y+Q i))) atTop (𝓝 0):=by
 have y(i:ℕ)(p:Y.s≤c i) : E! (c i) (Y.zoom P (c i) 3)=P.zt Y:= matchR (timeMesh P.par) _ _ _ p
 let v:= P.zt Y; let t:= v/2; have hv:0<v:=when_pos _ _ _ (Y.pos 3); have ht:0<t:=half_pos hv;
 have hdQ:Tendsto (fun i=> Q i) atTop (𝓝 0):= P.edelweiss 3 c r U Z
 let α(i):= E! (c i) (Y.zoom P (c i) 3-q' (r i))
 have hc: ∀ᶠ i in atTop,Y.s≤ c i ∧ Q i < t := (B.tendsto_atTop.eventually (eventually_ge_atTop Y.s)).and (hdQ.eventually (gt_mem_nhds ht))
 have hz(i)(p: Y.s≤c i ∧ Q i<t): q' (r i) < Y.zoom P (c i) 3:= lt_of_not_ge (fun h=>(p.2.trans_le (half_le_self hv.le)).not_ge ((y i p.1).ge.trans ((when_le ..).mpr h)))
 have h(i)(p:Y.s≤c i ∧ Q i<t): α i+Q i=v:=by
    have hp:= hz i p; unfold v; rw [←y i p.1]; unfold α whenly; rw [←add_mul,←Nat.cast_add,Nat.sub_add_cancel hp.le]
 have he:Tendsto α atTop (𝓝 v):=by
    have ht:= (tendsto_const_nhds (x:=v)).sub hdQ; rw [tsub_zero] at ht;
    exact ht.congr' (hc.mono fun i p=> (by rw [← h i p, add_tsub_cancel_right]))
 have hy:t+t=v:= add_halves v
 have htk:t<v:= half_lt_self hv
 have hZ:=he.eventually (lt_mem_nhds htk)
 let g(i):= P.swordA 3 V (P.thinMat Z (c i) (r i)) (α i) (E! (c i) (Y.zoom P (c i) 3))
 let f(i):=demerit Z • E (P.zt Y+P.zt Y+Q i)
 let F:=demerit Z • E (v+v)
 have hw:Tendsto g atTop (𝓝 F):=by
    have h':= P.sharpClub 3 c r U V Z t t ht ht (he.sub (tendsto_const_nhds (x:=t))) (A':=fun i=>α i-t) (B:=fun _=>t) (tendsto_const_nhds (x:=t))
    rw [hy, add_tsub_cancel_of_le htk.le] at h'; refine h'.congr' ?_
    filter_upwards [hc,hZ] with i p q; unfold g; rw [add_tsub_cancel_of_le (show t≤α i from q.le), y i p.1]
 have hx:Tendsto f atTop (𝓝 F):=by
    let l:=v+v; have ht:Tendsto (fun i:ℕ=>l+Q i) atTop (𝓝 l):=by simpa using hdQ.const_add l
    have hl:(0:ℝ)< (l:ℝ):=by unfold l; positivity
    have h:= Aria.steam_contPos (ℰ) l hl|>.tendsto.comp (NNReal.continuous_coe.continuousAt.tendsto.comp ht); rw [Real.toNNReal_coe] at h; exact (h.const_smul (demerit Z)).congr fun i=>by simp [comp_def,f,l,v]
 let w(i):= E (E! (c i) ((Y₀ (c i) (r i)).u 3))
 let y':= Y.engine P 3 V
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 have ht:Tendsto (fun i=> ‖y'‖*‖g i-f i‖) atTop (𝓝 0):=by simpa only [sub_self,norm_zero,mul_zero] using ((hw.sub hx).norm.const_mul ‖y'‖)
 apply squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) ?_ ht
 filter_upwards [hc] with i p
 rw [P.stitchEd x Z Y p.1 (hz i p)]
 change ‖w i*y'*g i - w i*y'* f i‖ ≤ _
 rw [←mul_sub]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans ((mul_le_mul_of_nonneg_right ((ℰ).shrinks _) (norm_nonneg _)).trans_eq (one_mul _))) (norm_nonneg _))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
