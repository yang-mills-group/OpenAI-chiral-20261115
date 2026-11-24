import GaugeFieldConstruction.Toddy
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
abbrev Agora(n:Side):= Seat n→ SU.E
variable (P:BudgetPoint)(F: Paper n)(g:Agora n)
variable {S:Hubber n}{h a:ℝ}
abbrev launchZ(s:Sweep n):UNI (Single n):= siteU (castX s) s.charge (spinU s.charge s.s) n
abbrev Typer(u:Sweep n):= detX u.s
abbrev GA (g:Agora n):Pane n→Pane n:= Lattice.gauge g
def portable (A:Paper n): Prop:= ∀ U:Pane n,∀ g:Agora n,αLines A (GA g U)=steerZ (tradew n g) false false (αLines A U)
def Barber (J:Sweep n)(A:Paper n):Paper n:= CardCraft (launchZ J) J.charge (Typer J) (flashA J⁻¹) A
def censusF(g:Agora n)(A:Paper n):Paper n:= CardCraft (tradew n g) false false (GA g⁻¹) A
lemma massTransitG(p:BudgetPoint): Transport (tradew n g) p (Equiv.refl _) (GA g⁻¹) S:=by
 refine ⟨fun i j h=> Tye.birth_g i j g h, fun F v m=>?_⟩; let g':=g⁻¹; let M:= GA g'; rw [show MustCap (Equiv.refl _) S=S from Finset.map_refl]; have hx: Continuous M:=by unfold M GA Lattice.gauge; refine continuous_pi fun j=>?_; fun_prop
 refine ⟨m.1,Env.along m.2.1 hx.measurable,fun i j p=>m.2.2.1 _ _ (fun e u V=> congrArg (fun i => g' _ *i * (g' _)⁻¹) (p e u V)),fun i u=>?_⟩
 let t:=p.threshold; let L:= swing (G:=SU.group) g'
 have hh:Allows p.order (F∘Shield.solo t (M i)) 0 v:=m.2.2.2 _ ((pingB _ _).mpr u)
 refine (comps L (x:=0) (map_zero L|>.symm ▸ hh) ?_).germ ?_ -- tune
 · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro a; rw [show ‖L i a‖=_ from swing_size g' i a]; exact norm_le_pi_norm i a
 refine Eventually.of_forall fun v=>congrArg F (show Shield.solo t (M i) (L v)=_ from ?_); unfold Shield.solo; rw [← map_smul, show L _= _ from rfl]; exact swing_increment _ i _
lemma massTransitS (s:Sweep n): Transport (launchZ s) P (boxA s) (flashA s⁻¹) S:=by
 refine ⟨fun i j h=> Tye.birth_l i j (castX s) (spinU s.charge s.s) s.charge h, fun F v m=>?_⟩
 let M:= flashA s⁻¹; let K:= MustCap (boxA s) S; have he(i x:Pane n)(p:Lattice.Agrees K i x):Agrees S (M i) (M x):=by apply flashD _ i x; rw [sitU]; exact p
 refine ⟨m.1,Env.along m.2.1 (revM s⁻¹).measurable,fun i x p=> m.2.2.1 (M i) (M x) (he i x p),fun i p=>?_⟩
 let t:= P.threshold; let L:= door_b s⁻¹ i; have ht:pingS t S (M i):=tape_C s S ▸ ((glowA t (actY s S) s⁻¹ i).mpr p)
 have hv: Allows P.order (F∘ Shield.solo t (M i)) 0 v:=m.2.2.2 _ ht; refine (comps L (x:=0) (map_zero L|>.symm ▸ hv) ?_).germ ?_
 · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i'; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro e; rw [show ‖L i' e‖=_ from cod_E s⁻¹ i i' e]; exact norm_le_pi_norm _ _
 refine Eventually.of_forall fun v=>congrArg F (show Shield.solo t (M i) (L v)=_ from ?_); unfold Shield.solo; rw [← map_smul]; exact (tour_p s⁻¹ i _).symm
-- algebra
lemma goZ(A:Pane n):GA g (GA g⁻¹ A)= A:=by unfold GA; rw [gauge_sq,mul_inv_cancel]; funext i; simp [Lattice.gauge]
lemma goS(s:Sweep n)(A: Pane n):flashA s (flashA s⁻¹ A)=A:=by simpa using revB s⁻¹ A -- order
lemma censusK (A:Pane n): αLines (censusF g F) (GA g A)=steerZ (tradew n g) false false (αLines F A):=by
 change steerZ _ _ _ (αLines F _)=_; rw [show GA g⁻¹ (GA g A)= A from by nth_rw 2 [← inv_inv g]; rw [goZ]]
lemma boothK (s:Sweep n)(A:Pane n): αLines (Barber s F) (flashA s A)=steerZ (launchZ s) s.charge (Typer s) (αLines F A):=by change steerZ _ _ _ (αLines F _)=_; rw [revB]
-- composition gcd coax
private lemma deckH (F H:Paper n)(p:∀ V,αLines F V=αLines H V):F=H:=funext fun i=>funext fun j=>congrFun (p j) i
lemma census_L(t: Agora n) : censusF g (censusF t F)=censusF (g*t) F:=by
 apply deckH; intro i; rw [← goZ (g*t) i]; let z:= GA (g*t)⁻¹ i; change αLines _ (GA (g*t) z)=αLines _ (GA (g*t) z)
 rw [censusK F, show GA (g*t) z=GA g (GA t z) from (gauge_sq ..).symm,censusK,censusK,convoyZ,show tradew n g*whiten false (tradew n t)=tradew n (g*t) from trade_c t g]; rfl
lemma census_Z : censusF 1 F= F:=by
 apply deckH; intro i; have he:GA (1:Agora n) i=i:=by funext; simp [GA,Lattice.gauge]
 nth_rw 1 [←he]; rw [censusK,trade_p,one_S]
lemma spin_auth (s:Sweep n)(A: UNI SpinIdx)(h:JetS s.s s.charge (Typer s) A)(X:ChartP n): steerZ (siteU (castX s) s.charge A n) s.charge (Typer s) X= steerZ (launchZ s) s.charge (Typer s) X:=by obtain ⟨z,p,t,w⟩:= Hive.king s.charge _ A (spinU s.charge s.s) h (spinZ ..); exact rayZ _ _ _ _ (Ygs _ _ _ p) t w _
private lemma spin_shape (x y:Sweep n)(A:ChartP n): steerZ (launchZ y) y.charge (Typer y) (steerZ (launchZ x) x.charge (Typer x) A)= steerZ (launchZ (x*y)) (x*y).charge (Typer (x*y)) A:=by
 rw [convoyZ]; let s:= x.charge; let t:=y.charge; let a:= castX x; let b:= castX y; let V:=spinU s a.s; let W:=spinU t b.s; let r:=s.xor t
 rw [show (x*y).charge=r from rfl] -- namespace
 rw [show x*y= ray r (joinX a b) from (by rw [←ray_join,show ray s a=x from ray_i x,show ray t b=y from ray_i y]), show (launchZ y)*whiten y.charge (launchZ x)=siteU (joinX a b) r (W*whiten t V) n from Levier.turns ..] -- shape turn order
 rw [show (Typer x ^^ Typer y)=Typer (ray r (joinX a b)) from (det_p a.s b.s).symm]
 refine Eq.trans ?_ (spin_auth _ (W*whiten t V) (shineU s a t V W _ (spinZ ..) (spinZ ..)) A); let D:= joinX a b; symm; let z:= fee (Rush.periods n (lift (wrap n D.t))- Rush.periods n D.t); exact rayZ _ _ _ _ (utu n r (W*whiten t V) D.s (lift (wrap n D.t)) D.t (wrap_lift _)) ((pow_two _).trans (fee_one _)) (fee_real _) _
lemma barber_L (x y:Sweep n): Barber y (Barber x F)=Barber (x*y) F:=by
 apply deckH; intro i; let s:= x*y; let u:= flashA s⁻¹ i; rw [← goS s i]; rw [boothK F s]; change αLines _ (flashA (x*y) u)= _; rw [←lights,boothK,boothK]; apply spin_shape
lemma barber_tru(g:Agora n)(s:Sweep n)(p:portable F): portable (Barber s F):=by
 intro i h; obtain ⟨x,rfl⟩:= (show Surjective (flashA s) from fun i=>⟨flashA s⁻¹ i,goS s i⟩) i; let a:= castX s; let V:=launchZ s; let L:Agora n:= fun i=> polarT s.charge (h ((boxA s).symm i)); have ht:h=(polarT s.charge ∘ L) ∘ a.anon n:=by funext i; change h i=polarT _ (L (boxA s i)); unfold L; simp only [Equiv.symm_apply_apply,polar_t,Bool.xor_self]; rfl -- tune
 rw [ht, show GA ((polarT s.charge ∘ L) ∘ a.anon n) (flashA s x)= flashA s (GA L x) from (revG s x L).symm,boothK,boothK, show αLines F _ = steerZ _ _ _ _ from p x L]; rw [convoyZ, convoyZ]; unfold launchZ; rw [tr_s]; simp only [site_ui,Bool.false_xor,Bool.xor_false,whiten,Bool.false_eq_true,↓reduceIte,envoy]; rfl
end MastTin
end YM.CF.XGarden
end
