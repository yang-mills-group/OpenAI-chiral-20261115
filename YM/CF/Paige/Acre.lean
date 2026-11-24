import YM.CF.Paige.Region
/-! Average full relative log. Carry kills the winding choices along output simplex. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Paige
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush Brace
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L: Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{B m r: Side}{e:ℝ}
variable (g:Grasp Y B e)(he:0<e)(G: Ratio (CSide m B) (CSide r B))(hc:G.count=L)(k:g.roundZ ≤(CSide m B).val)
variable(U:nomA m r B)(p:JointB G U e)(M:Tulip.Male)
def benchL (x: Sheen m B):ℂ:= firmL g G (accordL G U x) M- Matrix.trace (eExp T Y.k M G (post (accordL G U x)))
include k p hc he
lemma pose_g(x:Sheen m B)(h:Slow U.2 (hook x) g.baseline): SectorK g G (accordL G U x) :=by
 obtain ⟨he,hq⟩:=g.home r G hc he k U p x h; exact ⟨hq,p,he,fun i j=>(h i j).trans_le g.small⟩
lemma chant_price(x:Sheen m B)(h:Slow U.2 (hook x) g.baseline):
 Complex.exp (benchL g G U M x)=(sect0 G * chargeA T G M (unionP U))⁻¹ * skyGlow (sear g G U.2 (upMale L ho M)) (ticketT T true M G (unionP U)) (adjust g G U.1 M):=by
 let z:=accordL G U x; have ht:=pose_g g he G hc k U p x h
 let S:=sect0 G; let t:=Matrix.trace (eExp T Y.k M G (post z)); let V:=firmL g G z M
 have hz:chargeA T G M (unionP U)=Complex.exp t:= (Y.cap G hc (g.needed.trans k) M z ht.glyph).pay
 have he: skyGlow (sear g G U.2 (upMale L ho M)) (ticketT T true M G (unionP U)) (adjust g G U.1 M)=S*Complex.exp V:=hymn g G hc k _ ht _
 rw [he,hz]; change Complex.exp (_-_)=(S*_)⁻¹*_; have hs:S≠0:= norm_pos_iff.mp ((sectorU G).symm ▸ zero_lt_one); rw [Complex.exp_sub]; field_simp; exact mul_comm (Complex.exp V) _
omit he p in
lemma firm_c :ContinuousOn (fun x:sewA m r B=> firmL g G x M) {x|SectorK g G x}:=by
 let Z:=sewA m r B; let U: Set Z:={x|SectorK g G x}
 have hb (v: AxisT) (F:Chop Male)(h:IndexB L v v F Y.A Y.C Y.e Y.N): ContinuousOn (fun x:Z=> Matrix.trace (F M G (post x))) U:= continuous_id.matrix_trace.comp_continuousOn ((receipt_c G (A:=F M G) (h M G hc (g.needed.trans k)) Y.range).mono fun i h=> (show SectorK _ _ _ from h).glyph)
 let f:=fun x:Z=>(x.1.2,x.2.2); let S:=fun x:Z=>(x.1.1,x.2.1)
 have hx:= (song_c g.topB g.baseY.1 (g.couture k (upMale L ho M))).comp (f:=f) (by unfold f; fun_prop) (fun i (h:SectorK g G i)=>⟨h.cap.cg,h.loc⟩) -- y
 have hQ:= (song_c g.topB g.baseY.1 (g.couture (g.clock_fine G k) M)).comp (f:=S) (by unfold S; fun_prop) (fun i (h:SectorK g G i)=>⟨h.cap.fg,h.mist⟩)
 have he : ContinuousOn (fun x:Z=> bookL g G x M) U := (Complex.continuous_ofReal.comp_continuousOn ((Complex.continuous_re.comp_continuousOn (hb _ _ Y.projected)).div_const 4)).add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hx))) -- tune
 have hm : ContinuousOn (fun x:Z=> noteL g G x M) U := (Complex.continuous_ofReal.comp_continuousOn ((Complex.continuous_re.comp_continuousOn (hb _ _ Y.income)).div_const 4)).add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hQ)))
 exact ((hb _ _ Y.earningsK).add he).sub hm
omit p in
lemma bench_c : ContinuousOn (fun x:nomA m r B × Sheen m B=> benchL g G x.1 M x.2) {x| JointB G x.1 e∧Slow x.1.2 (hook x.2) g.baseline}:=by
 let s: Set (nomA m r B × Sheen m B):= {x| JointB G x.1 e ∧Slow x.1.2 (hook x.2) g.baseline}; let Z:= {x:sewA m r B|SectorK g G x}; let f (x:nomA m r B × Sheen m B) := accordL G x.1 x.2
 have he': Continuous f:=continuous_fst.prodMk (((ascent_c G).comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk continuous_snd)
 have hh:Set.MapsTo f s Z:=fun i h=>pose_g g he G hc k i.1 h.1 i.2 h.2
 have ht : ContinuousOn (fun x:sewA m r B=> Matrix.trace (eExp T Y.k M G (post x))) Z:= continuous_id.matrix_trace.comp_continuousOn ((receipt_c G (A:=eExp T Y.k M G) (Y.beauty M G hc (g.needed.trans k)) Y.range).mono fun _ h=>(show SectorK _ _ _ from h).glyph)
 exact ((firm_c g G hc k M).sub ht).comp he'.continuousOn hh
lemma refrain (x y:Cue m)(h:EdgeP m B U.2 x y): benchL g G U M (starfish m B U.2 x)=benchL g G U M (starfish m B U.2 y):=by
 let s:=Phase.twin m x y; let r:=insert 1 ({0}:Zone); let Z(q: Sq):= airing m B U.2 s q; let L(q:Sq):= benchL g G U M (Z q)
 have hp(q)(h':q∈zone r): Slow U.2 (hook (Z q)) g.baseline:= kleid g.capY p.cg he.le (r':=r) h h'
 have hs:ContinuousOn Z (zone r):=fun q h'=> ContinuousAt.continuousWithinAt ((air_at g.capY p.cg he.le (r':=r) (s:=s) h h').comp (f:=fun z:Sq=>(U.2,s,z)) (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt)
 have hb: ContinuousOn L (zone r):= (bench_c g he G hc k M).comp (f:=fun q=>(U,Z q)) (continuousOn_const.prodMk hs) fun i h=>⟨p,hp i h⟩
 let a:= (stick 0); have ha:a∈zone r:=stick_in _ (by simp [r]); let b:=stick 1; have hz:b∈zone r:= stick_in _ (by simp [r]);
 have hx:L a=L b:=carry_log (cube_path r).isPreconnected continuousOn_const hb a ha (v:=fun _=>L a) (fun y hy=>(chant_price g he G hc k U p M (Z a) (hp a ha)).trans (chant_price g he G hc k U p M _ (hp y hy)).symm) rfl b hz
 unfold L at hx; rw [show Z a=_ from risingV 0 s U.2 x (fun _=> rfl),show Z b=_ from risingV 1 s U.2 y (fun _=> rfl)] at hx; exact hx
lemma par4 (x y :Cue m)(u:ZeroF m B U.2 x)(v:ZeroF m B U.2 y): benchL g G U M (starfish m B U.2 x)=benchL g G U M (starfish m B U.2 y):=by obtain ⟨z,h,P⟩:=arches u v; rw [refrain g he G hc k U p M _ _ h,refrain g he G hc k U p M _ _ P]
def flakeL(U:nomA m r B)(M:Tulip.Male):ℂ:= ∫ x:Cue m, (law m B U.2 x:ℝ) • benchL g G U M (starfish m B U.2 x) ∂ rains m
lemma flake_par(x:Cue m)(u:ZeroF m B U.2 x): flakeL g G U M = benchL g G U M (starfish m B U.2 x):=by
 let A:= benchL g G U M (starfish m B U.2 x)
 unfold flakeL; rw [show (fun y:Cue m=> law _ _ _ y • benchL g G U M (starfish m B U.2 y))=fun y=>law m B U.2 y • A from ?_,integral_smul_const,rain_law,one_smul];
 funext y; by_cases h:law m B U.2 y=0; rw [h,zero_smul,zero_smul]
 rw [par4 g he G hc k U p M y x (law_rich m B U.2 y h) u];
lemma chargeR :Complex.exp (flakeL g G U M)=(sect0 G * chargeA T G M (unionP U))⁻¹ * skyGlow (sear g G U.2 (upMale L ho M)) (ticketT T true M G (unionP U)) (adjust g G U.1 M):=by
 obtain ⟨x,hx⟩:= cue_from U.2; rw [flake_par g he G hc k _ p _ x hx]; apply chant_price _ he _ hc k _ p ; exact starK g.capY he.le p.cg hx
end YM.CF.Paige
