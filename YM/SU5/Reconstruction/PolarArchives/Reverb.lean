import YM.SU5.Reconstruction.PolarArchives.Seafloor
/- Amplify the CP18 kernel proofs (adapt our Dr. ..) from just the fixed-FAR SINGLET stencils. Economical area. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open PolarArchives
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
variable (P:Ramp) {J: Calibration}
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
variable (gap:ℝ≥0)
local notation "Π" => Domain Y H G true (PolarArchives.Acres P gap)
local notation "S" => Domain Y H G true (PolarArchives.SkyAcres P gap)
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
variable (W:Chat_remote Y H V G P C a χ gap)
open _root_.YM.ConePrice.Storm.StepVoucher
local notation "Wr"=> stretchD P
local notation "📥"=> treks_remote Y H V G P gap
-- rite in planar charges. bound actual canonical spectator, no continuity needed from Backing
set_option maxHeartbeats 900000 in
lemma horizontal_cap_remote (x y:Π): ∃ D':ℝ,∃ K':ℝ,∀ r:↥(marks (timeMesh Λ)), K' ≤ (r:ℝ) → ∀ h:0≤(r:ℝ), ‖inner ℂ (W.plant x) (W.plant (treks_remote Y H V G P gap r h y))‖ ≤ D':=by
 let U₁:=gust P K x.val; have hu:= glides_N_remote Y H V G P gap x.property
 obtain ⟨B',e,c,p⟩:=(compact_domain Y H G).1 hu
 obtain ⟨T,w,gT,q⟩:=(compact_domain Y H G).1 y.property
 -- now approach long right identity with time a grants
 obtain ⟨u,tu⟩:=(e.image (show Continuous (fun x:RSpace=> x P.a) from continuous_apply _)).bddAbove
 obtain ⟨z,tz⟩:=(w.image (show Continuous (fun x:RSpace=> x P.a) from continuous_apply _)).bddBelow
 obtain ⟨b,vb⟩:= anywhere Λ (max u (-z))
 let f:= move K (Wr (-b) 0) U₁; let g:= move K (Wr b 0) y.val
 have tf: flipMark P.a K f∈ Domain Y H G false (flank P.a 0):= by
    refine reversed_fit Y H G P.a false _ (lowering Y H V G P.a (domain_loose Y H G _ p) (Wr (-b) 0) (fun x o=>?_)); have he:x P.a ≤ u := tu (mem_image_of_mem _ o); unfold stretchD; rw [terrain_time P.cross]; change _ + -(b:ℝ)≤_; linarith [le_max_left u (-z)]
 have tg: g∈Domain Y H G false (flank P.a 0):=by
    refine heightening Y H V G P.a (domain_loose Y H G _ q) (Wr b 0) (fun x o=>?_); have he:z ≤x P.a:= tz (mem_image_of_mem _ o); unfold stretchD; rw [terrain_time P.cross]; linarith [le_max_right u (-z)]
 let W₁:= (Os (P.a)) (⟨_,tf⟩:D false (flank P.a 0)); let W₂:= (Os (P.a)) (⟨_,tg⟩:D false (flank P.a 0)); refine ⟨‖W₁‖*‖W₂‖,b.val+b.val,fun r k h=>?_⟩
 let Z:=r-(b+b); have hz:0≤(Z:ℝ):=by unfold Z; push_cast; linarith
 let y':=treks_remote Y H V G P gap r h y
 rw [guide_remote Y H V G P C a χ gap W,← whiff_move Y H V G C a χ (on_Cover_remote Y H V G P gap x.property y'.property) (Wr (-b) 0)]
 change ‖Ω (au (Wr (-b) 0) (U₁ * au (Wr r r) y.val))‖≤_
 rw [move_prod (Wr (-b) 0) U₁ _, show au (Wr (-b) 0) (au (Wr r r) y.val)=au (Wr Z r) g from ?_]
 swap; · unfold g; rw [move_sum,move_sum,stretch_add,stretch_add]; unfold Z; rw [show -b+r=r-(b+b)+b from by abel,add_zero,zero_add]
 let Z₁:=(J₀ (P.a)); have T':= measure_dials Y H V G C a χ P.a tf tg P.cross Z r hz
 change ‖Ω (f * move K (stretchD P Z r) g)‖≤_; unfold stretchD; rw [T']
 let A:= (A₀ (P.a)).E (Real.toNNReal Z.val); let X₃:= ((U₀ (P.a)).track.crew ⟨P.b,P.cross⟩).play r W₂
 refine (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (show ‖A X₃‖≤‖W₂‖ from ?_) (norm_nonneg _)); unfold X₃
 have Y':= ((A.le_opNorm X₃).trans (mul_le_of_le_one_left (norm_nonneg _) ((A₀ (P.a)).shrinks _)))
 unfold X₃ at Y'; rw [Players.wins] at Y'; exact Y'

private lemma drake_phi_remote (X:Hilbert)(x:X)(φ:ℕ→X)(hx:∀ n:ℕ,inner ℂ (φ n) (φ n)=inner ℂ x (φ (2*n))) (H':BddAbove (Set.range (fun i=>‖φ i‖))) (n:ℕ) : ‖φ n‖≤‖x‖:=by
 let E':= Set.range (fun i=>‖φ i‖); have stepV(i): ‖φ i‖∈E':=mem_range_self _ -- tune min!
 let R:=sSup E';have e(i):‖φ i‖ ≤ R:= le_csSup H' (stepV i)
 have R':0≤R:=(norm_nonneg _).trans (e 0)
 have ξ: R ≤ Real.sqrt (‖x‖*R):=csSup_le ⟨_,stepV 1⟩ (by
    rintro _ ⟨n,rfl⟩; apply Real.le_sqrt_of_sq_le
    calc
       ‖φ n‖^2=‖inner ℂ x (φ (2*n))‖:=by rw [← hx,inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖φ n‖:ℝ):ℂ)‖^2; simp
       _≤_:= (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (e _) (norm_nonneg _)))
 have hc : R ≤ ‖x‖:=by nlinarith [norm_nonneg x,Real.sq_sqrt (show 0≤_ from mul_nonneg (norm_nonneg x) R')]; -- tune
 exact (e n).trans hc
private lemma confirm_v_remote {u v:Gt}(e:u=v)(x y)(f:Π): treks_remote Y H V G P gap u x f= treks_remote Y H V G P gap v y f:=by subst v; rfl
set_option maxHeartbeats 800000 in
lemma stieltjes_decrease_remote(t:Gt)(p:0≤(t:ℝ))(x:Π):‖W.plant (treks_remote Y H V G P gap t p x)‖ ≤ ‖W.plant x‖:=by
 rcases lt_or_eq_of_le p with p|p
 swap
 · obtain rfl : (0 :↥(marks (timeMesh Λ)))=t:= Subtype.ext p; rw [trek_zero_remote]
 obtain ⟨u,d,h⟩:= horizontal_cap_remote Y H V G P C a χ gap W x x
 let x'(n:ℕ):=(treks_remote Y H V G P gap (n•t) (cast_Δ t n p.le)) x; let φ(n:ℕ):=W.plant (x' n)
 have hx(n:ℕ): inner ℂ (φ n) (φ n)=inner ℂ (W.plant x) (φ (2*n)):= by
    have eq:0≤((n • t+n • t :Gt):ℝ):= add_nonneg (cast_Δ t _ p.le) (cast_Δ t _ p.le); unfold φ x'; rw [doubles_take_remote Y H V G P C a χ gap W x _ _ eq]; exact congrArg (fun z=>inner ℂ (W.plant x) (W.plant z)) (confirm_v_remote Y H V G P gap (show n • t+n • t=(2*n) • t by rw [two_mul,add_smul]) _ _ x)
 let E':= Set.range (fun i:ℕ=>‖φ i‖)
 have θ₁(i:ℕ): ‖φ i‖ ∈ E':= mem_range_self _
 have H':BddAbove E':=by
    apply Filter.IsBoundedUnder.bddAbove_range
    refine ⟨Real.sqrt u, Filter.eventually_map.mpr ?_⟩
    have v: Tendsto (fun n:ℕ=> ((2*n:ℕ):ℝ)*(t:ℝ)) atTop atTop:=(tendsto_natCast_atTop_atTop.comp (show Tendsto (fun n:ℕ=>2*n) atTop atTop from (show StrictMono (fun n:ℕ=>2*n) from by intro i j v; change 2*i<2*j; omega).tendsto_atTop)).atTop_mul_const p
    filter_upwards [v.eventually_ge_atTop d] with n zn
    have hp : ‖inner ℂ (W.plant x) (φ (2*n))‖ ≤ u:= h _ (show d ≤ (((2*n)• t:Gt):ℝ) from by rw [AddSubgroup.coe_nsmul,nsmul_eq_mul]; exact zn) (cast_Δ t (2*n) p.le)
    rw [← hx,inner_self_eq_norm_sq_to_K,norm_pow] at hp; change ‖((‖φ n‖:ℝ):ℂ)‖^2≤u at hp; simp only [Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)] at hp
    exact Real.le_sqrt_of_sq_le hp

 have ht : treks_remote Y H V G P gap t p.le x=x' 1:=Subtype.ext (by change au (Wr t t) _= au (Wr ((1:ℕ) • t) ((1:ℕ) • t)) _; rw [one_smul])
 rw [ht]; exact drake_phi_remote (W.H) (W.plant x) φ hx H' 1
lemma complicit_remote(t:Gt)(p:0≤(t:ℝ)):∃ L:W.H.Op,‖L‖≤1 ∧ (∀ x:Π, L (W.plant x)= W.plant (📥 t p x)):=extends_path (fanoForm_remote Y H V G P C a χ gap) W (treks_remote Y H V G P gap t p) (stieltjes_decrease_remote Y H V G P C a χ gap W t p)
noncomputable def radial_remote(t:Gt)(p:0≤(t:ℝ)): W.H.Op := (complicit_remote Y H V G P C a χ gap W t p).choose
lemma service_remote(t:Gt)(p:0≤(t:ℝ)): ‖radial_remote Y H V G P C a χ gap W t p‖≤1∧ ∀ x:Π, radial_remote Y H V G P C a χ gap W t p (W.plant x)= W.plant (📥 t p x):= (complicit_remote Y H V G P C a χ gap W t p).choose_spec
local notation "U" =>radial_remote Y H V G P C a χ gap W
lemma positive_speed_remote(t:Gt)(p:0≤(t:ℝ)): 0 ≤ U t p:= by apply pos_path (fanoForm_remote Y H V G P C a χ gap) W _; intro x; rw [(service_remote Y H V G P C a χ gap W t p).2]; exact monotone_v_remote Y H V G P C a χ gap W t p x
lemma speeds_up_remote(u v:Gt)(p q r): U u p * U v q = radial_remote Y H V G P C a χ gap W (u+v) r:= by
 apply W.by_bud; intro x; change U u p (U v q (W.plant x))= _; rw [(service_remote Y H V G P C a χ gap W v q).2,(service_remote Y H V G P C a χ gap W u p).2,(service_remote Y H V G P C a χ gap W _ r).2,trek_add_remote Y H V G P gap u v p q r]
private lemma close_radial_remote {u v:Gt}(p:u=v)(x y): radial_remote Y H V G P C a χ gap W u x= radial_remote Y H V G P C a χ gap W v y:=by subst v; rfl
private lemma zero_r_remote : radial_remote Y H V G P C a χ gap W 0 (by simp)=(1:W.H.Op):=by
 apply W.by_bud; intro x; refine ((service_remote Y H V G P C a χ gap W 0 (by simp)).2 x).trans ((congrArg W.plant (trek_zero_remote Y H V G P gap x)).trans rfl)
lemma ticks_remote(t:Gt)(p:0≤(t:ℝ))(n:ℕ) : (radial_remote Y H V G P C a χ gap W t p)^n= radial_remote Y H V G P C a χ gap W (n • t) (cast_Δ t n p):=by
 induction n with
 | zero=>
    rw [pow_zero, close_radial_remote Y H V G P C a χ gap W (zero_smul _ t : (0:ℕ)•t=0) (cast_Δ t 0 p) (show 0≤((0:Gt):ℝ) from le_rfl),zero_r_remote]
 | succ n ih=> rw [pow_succ,ih, speeds_up_remote Y H V G P C a χ gap W _ _ _ _ (show 0 ≤ ((n • t+t :Gt):ℝ) from add_nonneg (cast_Δ t n p) p)]; exact close_radial_remote Y H V G P C a χ gap W (by rw [add_smul,one_smul]) _ _
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
