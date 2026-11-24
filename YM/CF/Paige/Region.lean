import YM.CF.Paige.Grasp
/-! Unnormalized relative phases and exact output chart scalar. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Paige
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush Brace
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
section graph
variable {n:Type*}[Fintype n][LinearOrder n]{P Q W V K:Op n}{p q:Wave n}
lemma credit(h:Clad P Q W V K)(hp:Sea P p)(hq:Sea Q q)(a c s t :ℂ)(e:effectK (throat P Q W) (Complex.exp a • p)= Complex.exp c • (Complex.exp s • t • q)): skyGlow q W p=t*Complex.exp (c+s-a):=by
 unfold effectK at e; rw [map_smul, beam_plan h p q hp hq, smul_smul, smul_smul, smul_smul] at e
 have hb:= smul_left_injective ℂ (show q≠0 from norm_pos_iff.mp (hq.2.symm ▸ one_pos)) e
 change Complex.exp a*_= (_*_) at hb
 apply mul_left_cancel₀ (Complex.exp_ne_zero a); rw [hb,Complex.exp_sub,Complex.exp_add]; field_simp
end graph
variable {j:ℕ}{L: Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{B m r: Side}{e:ℝ}
variable (g:Grasp Y B e)(G: Ratio (CSide m B) (CSide r B))(hc:G.count=L)(k:g.roundZ ≤(CSide m B).val)
abbrev nomA(m r B:Side):=Nom (CSide m B) (CSide r B)
abbrev sewA(m r B:Side):= Sew (CSide m B) (CSide r B)
def tune (M:Tulip.Male) (U:Skin m B): Wave (Single (CSide m B)) := chant m B j M (g.cost m M) U
def adjust (U: Skin r B)(M:Tulip.Male): Wave (Iota G):= cartsL (switchG G).symm (chant r B j M (g.cost r M) U)
def sear (U:Skin m B)(M:Tulip.Male): Wave (Iota G):= hoist (patchQ G) (reefS G true) (tune g M U)
-- exact output log, before integration
def noteL (U:sewA m r B)(M:Tulip.Male):ℂ:= ((iExp j M G (post U)).trace.re/4:ℝ)+Complex.I*(song r B (g.cost r M) U.1.1 U.2.1).im
def bookL (U:sewA m r B)(M:Tulip.Male):ℂ:= ((fExp j L ho M G (post U)).trace.re/4:ℝ)+Complex.I*(song m B (g.cost m (upMale L ho M)) U.1.2 U.2.2).im
def firmL (U:sewA m r B)(M:Tulip.Male):ℂ:= Matrix.trace (cExp j L ho T Y.n M G (post U)) + bookL g G U M-noteL g G U M
structure SectorK (x:sewA m r B):Prop where
 glyph :Gild G x Y.e
 cap :JointB G x.1 e
 mist :Slow x.1.1 (hook x.2.1) g.p
 loc : Slow x.1.2 (hook x.2.2) g.p
variable (x:sewA m r B)(hx:SectorK g G x)(M:Tulip.Male)
include k hx hc
lemma earnedF :
 filled (foal j true M G (post x).1) (squareD G true (post x))=Complex.exp (noteL g G x M) • adjust g G x.1.1 M:=by
 let A:=cartsL (switchG G).symm; let v:= coneP j M x.1.1 x.2.1
 have he : filled (foal j true M G (post x).1) (squareD G true (post x))=A v:=by
   rw [square_true]; exact relabelF (switchG G).symm (starC (hook x.2.1 ∘ node) (fun i=>hookN ..)) ((g.broadness _ (g.clock_fine G k) M).projection _ hx.cap.fg) -- tune
 let c:= (iExp j M G (post x)).trace.re/4; have ht :‖v‖=Real.exp c:=by
   have hv := (Y.cap G hc (g.needed.trans k) M x hx.glyph).lit; rw [he,carts_n] at hv; exact hv.symm
 have hk:=phaseLift g.topB g.baseY.1 (g.couture (g.clock_fine G k) M) x.1.1 hx.cap.fg x.2.1 hx.mist c ht
 rw [he,show v= _ from hk]; unfold A; rw [carts_s]; rfl -- tune
lemma earnedC : filled (wh j L ho true M G (post x).1) (squareD G false (post x))=Complex.exp (bookL g G x M) • sect0 G • sear g G x.1.2 (upMale L ho M):=by
 let f:=upMale L ho M; let H:=hoist (patchQ G) (reefS G true); let v:=coneP j f x.1.2 x.2.2
 have hz:Guard x.1.2 e:=hx.cap.cg
 have he:filled (wh j L ho true M G (post x).1) (squareD G false (post x))= sect0 G • H v:=by rw [pierce]; exact sec_salary G ((g.broadness _ k f).projection _ hz) x -- tune dp
 let c:= (fExp j L ho M G (post x)).trace.re/4; have hv:= (Y.cap G hc (g.needed.trans k) M x hx.glyph).rod
 rw [he,norm_smul,sectorU,one_mul] at hv; have hl: ‖v‖=Real.exp c:= (hoistN _ _ (reefS_deck ..) v).symm.trans hv.symm
 have hk:=phaseLift g.topB g.baseY.1 (g.couture k f) x.1.2 hx.cap.cg x.2.2 hx.loc c hl
 rw [he,show v= _ from hk, map_smul,smul_comm]; rfl -- check
lemma harmony : Sea (foal j true M G (post x).1) (adjust g G x.1.1 M) ∧ Sea (wh j L ho true M G (post x).1) (sear g G x.1.2 (upMale L ho M)):=by
 let V:=Y.cap G hc (g.needed.trans k) M x hx.glyph
 constructor
 · exact carts_sea (switchG G).symm V.projP (heartS g.topB g.baseY.1 (g.couture (g.clock_fine G k) M) x.1.1 hx.cap.fg V.projP)
 rw [pierce]; exact stageUp _ _ (reefS_deck ..) V.projN (heartS g.topB g.baseY.1 (g.couture k _) x.1.2 hx.cap.cg V.projN)
lemma hymn : skyGlow (sear g G x.1.2 (upMale L ho M)) (ticketT T true M G (post x).1) (adjust g G x.1.1 M)= sect0 G * Complex.exp (firmL g G x M):=by
  let V:=Y.cap G hc (g.needed.trans k) M x hx.glyph
  obtain ⟨u,p⟩:= harmony g G hc k x hx M; unfold firmL
  apply credit (court _ _ _ _ _ _ _ (V.chart true)) u p; have he:=V.sea; rw [earnedF g G hc k x hx,earnedC g G hc k x hx] at he; exact he
end YM.CF.Paige
