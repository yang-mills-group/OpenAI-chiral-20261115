import WakeRoad.Admit
import WakeRoad.Long
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
variable {β:ℕ→ℝ} {I:ℝ}
local notation "W_"=>P.calibration
local notation "R" s:max=>zoomR P.par I s
-- unscaled & weight versions
abbrev tableT (P:Spine)(β:ℕ→ℝ)(I:ℝ)(D:Fin n→ PlaqAxes)(u:Fin n→ Cover)(s:ℕ): Family P.calibration :=
    (staffWeight (zoomR P.par I s))^n • household P.calibration (crewFilm (troops (0:Fin n→Twah.DirSpin) D (fun _=> u)) P β 4 s)
abbrev decks (u:Fin n→ Cover) := univ.biUnion fun i=>skyDeck (nodeC (u i)) 12
lemma table_license (D:Fin n→ PlaqAxes)(u:Fin n→ Cover)(s:ℕ) : InTest W_ true (decks u) false (tableT P β I D u s):= by
 apply InTest.smul; let f(i:Fin n):= choiceWeave P β (localStaff (u i) 0 (D i)) 4 s
 suffices h : InTest W_ true (decks u) false (YM.WakeRoad.serve (fun i=>household W_ (f i))) by
    have hp:household W_ (YM.WakeRoad.serve f)=YM.WakeRoad.serve (fun i=>household W_ (f i)):= serve_house f P
    change InTest _ _ _ _ (household W_ (YM.WakeRoad.serve f)); rwa [hp]
 exact generic (fun i=> household W_ (f i)) (fun i=> ((localStaff (u i) 0 (D i)).letterBudget (κFix β s) _ (temp (hat P.par.R.L P.par.x s)) (ready_local ..)).mono (subset_biUnion_of_mem (fun j=>skyDeck (nodeC (u j)) 12) (mem_univ i)))
where
 generic{n:ℕ}{A:Calibration}{S:Finset Cover}(f:Fin n→ Family A)(p:∀ i,InTest A true S false (f i)):InTest A true S false (YM.WakeRoad.serve f):= by induction n with|zero=> exact InTest.one|succ n h=> rw [YM.WakeRoad.steam]; exact (p 0).mul (h _ fun i=> p i.succ)
 serve_house{n:ℕ}(f:Fin n→ Weaver)(P:Spine):household P.calibration (YM.WakeRoad.serve f)=YM.WakeRoad.serve (fun i=> household P.calibration (f i)):=by induction n with|zero=> rfl|succ n ih=>rw [YM.WakeRoad.steam,YM.WakeRoad.steam]; change household P.calibration (f 0*(YM.WakeRoad.serve (f∘Fin.succ)))=household P.calibration (f 0)*(YM.WakeRoad.serve (fun i=>household P.calibration (f i.succ))); rw [←show household P.calibration (YM.WakeRoad.serve (f∘Fin.succ))= (YM.WakeRoad.serve (fun i=>household P.calibration (f i.succ))) from ih _]; rfl

lemma table_flight (V:Fin n→ Gaia)(u:ℕ→ Fin n→ Cover)(p:0<I)(h:∀ i,Appoint P.par I (fun s=>u s i) (V i)) (m:ℕ)(t:∀ i,0<gait P.par (V i) m 3):
    ∀ᶠ s:ℕ in atTop, region 3 0 (W_).ℓ (onFlight P.par.block (decks (u s)) 3 (kroll P.par I m s)):= by
 filter_upwards [Filter.eventually_all.mpr (fun i:Fin n=> cover_shelter p (h i) m (t i))] with s he v k
 obtain ⟨z,hz,rfl⟩:=mem_image.mp k; obtain ⟨i,x,u'⟩:=mem_biUnion.mp hz
 exact he i _ (mem_image_of_mem _ u')

abbrev πWave (u:Fin n→ Cover)(P:Preparation)(I:ℝ)(m s:ℕ):= forward u P I m s
lemma table_shifts (D:Fin n→ PlaqAxes)(u:Fin n → Cover)(s m:ℕ)(z:∀ i, (D i).val.1≠(3:Axis)∧ (D i).val.2≠3):
    let A:=table_license (β:=β) (P:=P) (I:=I) D u s; let f:=P.art _ (aux_test A); let v:= P.halfShift 3 (kroll P.par I m s) f
    v.val = tableT P β I D (πWave u P.par I m s) s := by
 intro A f v; change mirror _ 3 _ (mirror _ 3 0 ((staffWeight _)^n • _))= _
 rw [mirror_scale,mirror_scale,star_star]; congr 1
 change household W_ (takeoff P.par.block (YM.WakeRoad.serve (fun i:Fin n=> tee P β s (u i) (D i))) 3 (kroll P.par I m s))= household W_ (YM.WakeRoad.serve (fun i:Fin n=> tee P β s _ (D i)))
 let r:= kroll P.par I m s
 have he{n:ℕ}(f:Fin n→ Weaver)(x:ℤ): fluent 3 x (YM.WakeRoad.serve f)= YM.WakeRoad.serve (fluent 3 x ∘ f):= by
    induction n with
    | zero=>funext N X; exact theta_one _
    | succ n ih=> rw [YM.WakeRoad.steam,YM.WakeRoad.steam,vocal_two, ih]; rfl
 unfold takeoff traction; rw [he,he]; apply congrArg; apply congrArg; funext i; exact mover P β s _ (z i).1 (z i).2 r (u i)

lemma table_opp (D:Fin n→ PlaqAxes)(u:Fin n → Cover)(s:ℕ)(z:∀ i, (D i).val.1≠(3:Axis)∧ (D i).val.2≠3): mirror W_ 3 0 (tableT P β I D u s)=tableT P β I D (Shuttle.flip∘u) s:=by
 unfold tableT; rw [mirror_scale,show star ((staffWeight (R s))^n)=(staffWeight (R s))^n from ?_]; swap; · simp [star_mul,staffWeight,star_pow,mul_comm]
 change _ • household W_ (fluent 3 0 (YM.WakeRoad.serve (fun i:Fin n=> tee P β s (u i) (D i))))= _; congr 2
 -- goal after congr
 have he{n:ℕ}(f:Fin n→ Weaver): fluent 3 0 (YM.WakeRoad.serve f)= YM.WakeRoad.serve (fluent 3 0 ∘ f):= by
    induction n with| zero=> funext N X; exact theta_one _|succ n h=> rw [YM.WakeRoad.steam,YM.WakeRoad.steam,vocal_two,h]; rfl
 rw [he]; exact congrArg YM.WakeRoad.serve (funext fun i=> opposedT P β s _ (z i).1 (z i).2 (u i))

#print axioms table_shifts
#print axioms table_license
lemma table_joint2 (D:Fin 2→ PlaqAxes)(E:Fin 2→ PlaqAxes)(u v:Fin 2 → Cover)(s:ℕ): tableT P β I D u s *tableT P β I E v s=tableT P β I (Fin.append D E) (Fin.append u v) s:=by
 unfold tableT; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul, ← pow_add]; congr 1
 let f {m:ℕ}(F:Fin m→PlaqAxes)(u:Fin m→ Cover)(i:Fin m):= tee P β s (u i) (F i)
 have ht:f (Fin.append D E) (Fin.append u v)= Fin.append (f D u) (f E v):= funext (fun i=>by cases i using Fin.addCases<;> unfold f <;> simp only [Fin.append_left,Fin.append_right])
 change _= household W_ (YM.WakeRoad.serve (f (Fin.append D E) (Fin.append u v))); rw [ht]; unfold YM.WakeRoad.serve; rw [List.ofFn_fin_append,List.prod_append]; rfl

lemma table_price (D:Fin n→PlaqAxes)(a:ℕ→Fin n→ Cover)(s:ℕ): P.E s (tableT P β I D (a s) s)=partyValue (0:Fin n→Ballad.Twah.DirSpin) D a P β I s:=by
 unfold tableT partyValue; rw [E_scale P.run P.large P.law s (tag_crew _ (fun i s=> ready_local _ _ _) s)] -- matcher

def ballotDuet (P:Spine)(D:Fin 2→ PlaqAxes)(u:Fin 2 → Cover)(β:ℕ→ℝ)(I:ℝ)(s:ℕ): P.Test:=P.art (tableT P β I D u s) (aux_test (table_license D u s))

-- use motion & P.E positivity at shifted test. uniform connection even subtracting marginal constant
variable (D:Fin 2→ PlaqAxes)(hz:∀ i, (D i).val.1≠(3:Axis)∧ (D i).val.2≠3)(u:Fin 2→ Cover)(s m:ℕ)(T:region 3 0 P.calibration.ℓ (onFlight P.par.block (decks u) 3 (kroll P.par I m s)))
include T hz
lemma table_credit (b:ℂ):
    let χ:=fun x:P.Spectrum0 3=>P.singleState 3 s x (ballotDuet P D u β I s)
    let V:=tableT P β I D u s; let p:=πWave u P.par I m s; let q:= Shuttle.flip ∘ p
    (∫ x:P.Spectrum0 3, ‖χ x-b‖^2 ∂P.pillars 3)≤ ‖P.E s (tableT P β I (Fin.append D D) (Fin.append q p) s) - b * star (P.E s V) - star b*P.E s V+star b*b‖ ∧
    P.E s (tableT P β I D q s)=star (P.E s V) ∧ P.E s (tableT P β I D p s)= P.E s V:= by
 intro χ V p q; let S:=decks u; let z:=kroll P.par I m s; let F:= V-b • (1:Family P.calibration); let A:= table_license (β:=β) (P:=P) (I:=I) D u s
 have ht: InTest W_ true S false F:=by unfold F; rw [sub_eq_add_neg,←neg_one_smul ℂ (b • (1:Family W_))]; exact .add A (.smul _ (.smul _ .one))
 let v:=P.art F (aux_test ht); let t:=ballotDuet P D u β I s; have hp:v=t-b • 1:=Subtype.ext rfl
 let Xb:=P.halfShift 3 z t; let w :=tableT P β I D p s; let g:=tableT P β I D q s
 have hv:Xb.val=w:=table_shifts D u s m hz; have hθ:mirror W_ 3 0 w=g:=table_opp D p s hz
 let E:=P.E s
 have He: E w= E V:=hv ▸ (SWay P.run P.large P.law s 3 z (aux_test A))
 have k0:gaugeShift P.par.block (0:ℤ)=0:=by unfold gaugeShift; simp
 have he:E g=star (E w):=by
    rw [← hθ,← k0]; apply mirror_band P.run P.large P.law; let j:= onFlight P.par.block S 3 z
    refine ⟨j,?_,?_⟩
    · exact hv ▸ (Tapestry.locates ..).mp (P.shift_cover3 3 A z)
    rw [k0]; exact T
 refine ⟨?_,he.trans (congrArg star He),He⟩
 have Hy (x:P.Spectrum0 3):χ x-b=P.singleState 3 s x v:=by rw [hp,map_sub,map_smul,show (P.singleState 3 s x) 1=1 from (by simp [Spine.single_state]),smul_eq_mul,mul_one] --
 simp_rw [Hy]; apply (P.creditShelf 3 ht s z T).trans; change ‖E (mirror _ _ _ ((P.halfShift 3 z v).val)*(P.halfShift 3 z v).val)‖ ≤ _
 rw [hp,map_sub,map_smul,map_one]; change ‖E (mirror W_ 3 0 (Xb.val-b • 1)*(Xb.val-b • 1))‖≤_; rw [hv]
 have hm(F G:Family W_): mirror W_ 3 0 (F-G)=mirror W_ 3 0 F -mirror W_ 3 0 G:=funext fun n=>funext fun x=>theta_sub ..
 have hx: TestFamily W_ true w:= aux_test (table_license ..); have hg:TestFamily W_ true g:=aux_test (table_license ..); let h1:= TestFamily.oneT (K:=W_) (wide:=true)
 have HS{l r:Family W_}(p:TestFamily W_ true l)(q:TestFamily W_ true r):TestFamily W_ true (l-r):= by rw [sub_eq_add_neg,←neg_one_smul ℂ]; exact p.add (q.scale _)
 have hL:(g-star b • 1)*(w-b • 1)=g*w-b • g-star b • w + (star b*b) • (1:Family W_):=by simp only [_root_.sub_mul,mul_sub,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,mul_one,smul_sub,smul_smul,mul_comm b (star b)]; abel -- comm star b
 rw [hm, show mirror W_ 3 0 (b • (1:Family W_))= star b • mirror W_ 3 0 1 from mirror_scale ..,show mirror W_ 3 0 (1:Family W_)=1 from funext fun n=>funext fun x=>theta_one _,hθ,hL]
 have Hr:= HS (HS (hg.mul hx) (hg.scale b)) (hx.scale (star b)); unfold E; rw [E_add P.run P.large P.law s Hr (h1.scale (star b*b)),E_sub P.run P.large P.law s (HS (hg.mul hx) (hg.scale b)) (hx.scale _),E_sub P.run P.large P.law s (hg.mul hx) (hg.scale b),E_scale P.run P.large P.law s hg,E_scale P.run P.large P.law s hx, E_scale P.run P.large P.law s h1,E_unit P.run P.large P.law s,show g*w=_ from table_joint2 D D q p s]; unfold E at He he; rw [he,He,mul_one]
#print axioms table_credit

omit T
include hz
variable {f':ℕ→ℕ} (Q: Spine.PreparedInvestment P K E Mc) (HM:Pooling P.run (P.period∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f' β)
variable {O:Fin 2→ Gaia}(u':ℕ→Fin 2→ Cover) (p:0<I)(h:∀ i,Appoint P.par I (fun s=>u' s i) (O i))(t: Injective O)
local notation "jp" m:max => fun i:Fin 2=> gait P.par (O i) m
local notation "bX" => duoTarget O (0:Fin 2→Ballad.Twah.DirSpin) D
local notation "jX" m:max => Fin.append (Shuttle.opposite ∘ (jp m)) (jp m)
local notation "gX" m:max => galaTarget (jX m) 0 (Fin.append D D)
include Q HM p h t
lemma duet_poll: Spine.WakePoll P (fun s=> ballotDuet P D (u' s) β I s) (bX):=by
 let K:= (bX); let A(s):=P.E s (tableT P β I D (u' s) s)
 let f(m s):=πWave (u' s) P.par I m s; let g(m s):= Shuttle.flip ∘ f m s
 let V(m):= jp m; let U(m):= Shuttle.opposite ∘ V m
 let Y:= Shuttle.opposite∘O; let S:=duoTarget Y 0 D
 have hu(m):Injective (V m):=fun i j h=>t (add_right_cancel h); have ht(m):Injective (U m):=flip_inj.comp (hu m); have hz':Injective Y:=flip_inj.comp t
 have he(m i): Appoint P.par I (fun s=> f m s i) (V m i):= xplus_a p (h i) m
 have hk(m i): Appoint P.par I (fun s=> g m s i) (U m i):= xflip_a (he m i)
 have vp(m i j): V m i-V m j=O i-O j:=gait_d ..
 have up(m i j): U m i-U m j= Y i-Y j:=by unfold U Y; simp only [Function.comp_apply,flip_d,vp]
 have board(A B:Fin 2→ Gaia)(h:∀ i j,A i-A j=B i-B j):duoTarget A 0 D=duoTarget B 0 D:=by unfold duoTarget; apply sum_congr rfl; intro a _; simp only [hardCoin,Hearth.schedule,h]; congr 2; funext i j; simp only [spinOrbit,h]
 have ha:Tendsto A atTop (𝓝 K):=(afternoon Q HM u' 0 D p h t).congr fun s=> (table_price D u' s).symm
 have gt:∀ᶠ m:ℕ in atTop,∀ i,0<V m i 3:= Filter.eventually_all.mpr fun i=> (gait_up P.par (O i)).eventually_gt_atTop 0
 have hm(m:ℕ)(b:ℂ)(hm:∀ i,0<V m i 3): ∀ᶠ s:ℕ in atTop,
      (let x(s:ℕ):=tableT P β I D (g m s) s;(∫ x:P.Spectrum0 3, ‖P.singleState 3 s x (ballotDuet P D (u' s) β I s)-b‖^2 ∂P.pillars 3)≤ ‖P.E s (tableT P β I (Fin.append D D) (Fin.append (g m s) (f m s)) s)-b*star (A s)- star b*A s+star b*b‖ ∧ P.E s (x s)=star (A s) ∧ P.E s (tableT P β I D (f m s) s)=A s):=by filter_upwards [table_flight O u' p h m hm] with s hs; exact table_credit D hz (u' s) s m hs b
 obtain ⟨m,y⟩:= gt.exists
 have hs:S=star K:=by
    have hx:Tendsto (fun s=>P.E s (tableT P β I D (g m s) s)) atTop (𝓝 (duoTarget Y 0 D)):= (board (U m) Y (up m)) ▸ ((afternoon Q HM (g m) 0 D p (hk m) (ht m)).congr fun i=> (table_price D (g m) i).symm)
    exact tendsto_nhds_unique hx (ha.star.congr' ((hm m 0 y).mono fun s h=> h.2.1.symm))
 constructor; intro ε v
 have hx:= gala_factor Y O U V D D up vp (fun i j=>(foreign P.par (O i) (O j)).congr (fun _=> dist_eq_norm ..))
 change Tendsto _ _ (𝓝 (S*K)) at hx; rw [hs] at hx
 obtain ⟨m,e,p'⟩:= ((Metric.tendsto_nhds.mp hx ε v).and gt).exists
 let W:= Fin.append (U m) (V m); let J(s):=Fin.append (g m s) (f m s); let Q':=Fin.append D D
 have he': Injective W:=by
    intro i j; cases i using Fin.addCases <;> cases j using Fin.addCases
    · simp only [W,Fin.append_left]; intro e; exact congrArg (Fin.castAdd _) (ht m e)
    · next i j=> simp only [W,Fin.append_left,Fin.append_right]; intro e; have hx:=congrArg (fun x:Gaia=> x 3) e; have hh:U m i 3<0:= by change Shuttle.opposite _ 3<_; rw [opp_tim]; exact neg_neg_of_pos (p' i)
                 exact (not_le_of_gt (p' j) (e ▸ hh.le)).elim
    · next i j=> simp only [W,Fin.append_left,Fin.append_right]; intro e; have hk: U m j 3<0:=by change Shuttle.opposite _ 3<_; rw [opp_tim]; exact neg_neg_of_pos (p' j)
                 exact (not_le_of_gt (p' i) (e.symm ▸ hk.le)).elim
    simp only [W,Fin.append_right]; intro e; exact congrArg (Fin.natAdd _) (hu m e)
 have H(i:Fin 4): Appoint P.par I (fun s=>J s i) (W i):= by
    cases i using Fin.addCases (m:=2) (n:=2) with
    | left i=> simpa only [W,J,Fin.append_left] using hk m i
    | right i=> simpa only [W,J,Fin.append_right] using he m i
 have ht:Tendsto (fun s=> ‖P.E s (tableT P β I Q' (J s) s)- K*star (A s)- star K*A s + star K*K‖) atTop (𝓝 (dist (gX m) (star K*K))):=by
    have hu:Tendsto (fun s=>P.E s (tableT P β I Q' (J s) s)) atTop (𝓝 (gX m)):= (evening Q HM J 0 Q' p H he').congr fun s=> (table_price Q' J s).symm; rw [dist_eq_norm, show (gX m)-star K*K=(gX m)-K*star K-star K*K + star K*K by ring]; exact (((hu.sub ((ha.star).const_mul K)).sub (ha.const_mul _)).add_const _).norm
 filter_upwards [hm m K p', ht.eventually (gt_mem_nhds e)] with s u v; exact u.1.trans_lt v
#print axioms duet_poll
#check @duet_poll
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
