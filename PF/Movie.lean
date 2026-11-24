import PF.Pose
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.Vessel
open Acorn Hive Jet Pose Tenant Dial Paige
-- uniform slowdown for tangent vector. fundamental repr title line. Gives all derivative orders. 
private abbrev repr (z:SU.group.Color):Op SU.F:=SU.group.colorMat z
private noncomputable def assign : SU.group.Color →L[ℝ] Op SU.F := SU.group.colorMat.toContinuousLinearMap -- norm instance issues Frob restrict

noncomputable def deter:= (max (‖assign‖) 1)⁻¹
lemma deter_pos:0<deter:= inv_pos.mpr (lt_max_of_lt_right zero_lt_one)
lemma assigned (z:SU.group.Color)(h:‖z‖ ≤ deter) : ‖repr z‖≤1:=by
 let v:=max ‖assign‖ 1; have hv:0<v:=lt_max_of_lt_right zero_lt_one
 exact (assign.le_opNorm _).trans ((mul_le_mul (le_max_left ..) h (norm_nonneg _) hv.le).trans_eq (mul_inv_cancel₀ hv.ne'))

variable {n:Side}
private lemma scalarJet (T:ℝ→Op SU.F)(A:Op SU.F)(h:∀ t:ℝ,HasDerivAt T (A*T t) t)(v:∀ t, ‖T t‖=1)(q:‖A‖ ≤1)(k:ℕ)(t:ℝ): Allows k T t 1:=by
 have he (n:ℕ): iteratedDeriv n T=fun t=> A^n*T t:=by
    induction n with
    | zero=>ext1; simp
    | succ i p=>
      rw [iteratedDeriv_succ,p]; funext x; rw [((h x).const_mul (A^i)).deriv, ←mul_assoc,pow_succ]
 have ht(i:ℕ): Differentiable ℝ (iteratedDeriv i T):=by rw [he]; exact fun x=> ((h x).const_mul _).differentiableAt
 have hh: ContDiff ℝ (k:WithTop ℕ∞) T:= by
    rw [show (k:WithTop ℕ∞)= ((↑k:ℕ∞):WithTop ℕ∞) from rfl]; exact contDiff_iff_iteratedDeriv.mpr ⟨fun i _=> (ht i).continuous,fun i _=>ht i⟩
 refine ⟨hh.contDiffAt,fun j _=>?_⟩
 rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,he]; refine (norm_mul_le ..).trans ((mul_le_mul ((norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) q j).trans_eq (one_pow _))) (v _).le (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

private lemma turn_f (z:SU.group.Color)(t:ℝ): SU.fund (SU.group.lieExp (t • z)) = exp (t • repr z):=by
 rw [show SU.fund (SU.group.lieExp (t • z))=SU.group.mat (SU.group.lieExp (t • z)) from rfl,Gauge.mat_lieExp,map_smul]; rfl
private lemma fund_p (x:SU.E): ‖SU.fund x‖=1:= CStarRing.norm_of_mem_unitary (firstF x).property
lemma closeAngle (z:SU.group.Color)(u:‖z‖ ≤ deter)(B:Pane n)(v:gaugeLink n)(b:Bool)(t:ℝ)(k:ℕ) : Jet.TransK k (fun t:ℝ=> Pose.swing v b (t • z) B) t 1 :=by
 intro i; by_cases h:i=v
 · subst i; unfold Pose.swing; simp_rw [one_on]
   cases b with
   | false=>
     simp only [Bool.false_eq_true,↓reduceIte,mul_one,fund_mul,turn_f]
     let X:Op SU.F:=repr z
     apply scalarJet _ X; · intro t; have he:= (hasDerivAt_exp_smul_const X t).mul_const (SU.fund (B v)); rw [← ((Commute.refl X).smul_left t|>.exp_left).symm.eq] at he; rwa [←mul_assoc] -- tune commute syntax
     · intro t; rw [←turn_f, ←fund_mul]; exact fund_p _
     exact assigned z u
   | true=>
     simp only [↓reduceIte,one_mul,fund_mul,fund_inv,turn_f, star_exp,star_smul,star_trivial]
     let X:=star (repr z); let W:= firstF (B v); let C:= W.val * X * star W.val
     apply scalarJet _ C; · intro t; have he:= (hasDerivAt_exp_smul_const X t).const_mul W.val; rw [((Commute.refl X).smul_right t |>.exp_right).eq.symm] at he
                            convert! he using 1; change C*(W.val*exp (t • X))= W.val*(X*exp (t • X)); unfold C; simp only [mul_assoc]; rw [←mul_assoc (star W.val),W.property.1,one_mul]
     · intro t; rw [←show star (t • repr z)=t • X by rw [star_smul,star_trivial], ←star_exp,←turn_f,←fund_inv, ←fund_mul]; exact fund_p _
     unfold C; change ‖↑W * X * (↑(star W):Op SU.F)‖ ≤ (1:ℝ)
     exact (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans ((mul_le_mul (CStarRing.norm_of_mem_unitary W.property).le ((show ‖X‖= ‖repr z‖ from norm_star _).le.trans (assigned z u)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))) (CStarRing.norm_of_mem_unitary (star W).property).le (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
 simp_rw [Pose.swing,one_off _ _ h]; exact allows_const t (fund_p _).le

variable {m B : Side}{e d r:ℝ}
local notation "N"=>CSide m B
-- Castle construction all queries. proper Bool ordering.
variable (v:gaugeLink (CSide m B))(b:Bool)
private abbrev castleT (m B:Side)(v:gaugeLink (CSide m B))(e:ℝ):= Castle m B e (Skye.ends v)
private noncomputable def fixed (G:Pane (CSide m B))(p:Cube.Guard G e)(z:SU.group.Color)(t:Cube.Guard (Pose.swing v b z G) e): castleT m B v e := ⟨fun j=> if j then Pose.swing v b z G else G, by
  refine ⟨fun i=>?_,?_⟩
  · cases i; exact p; exact t
  intro i s y; have hi : i≠v:=fun t=> (Finset.mem_compl.mp s) (by rw [t]; simp)
  change G i=(if true=true then Pose.swing v b z G else G) i; rw [if_pos rfl]; exact (one_off _ _ hi G).symm⟩ -- lemma non Prop; def; mono structure prop? nested tuple
lemma zeroSwing (G:Pane (CSide m B)):Pose.swing v b 0 G=G:=by funext i; by_cases h:i=v; subst i; unfold Pose.swing; cases b <;> simp [one_on,Gauge.mat_lieExp_zero]; exact one_off _ _ h G
set_option maxHeartbeats 100000
private noncomputable def cruise (G:Pane (CSide m B))(w:d≤e)(p:Cube.Guard G d)(z:SU.group.Color)(x:ℝ):castleT m B v e:= by
 classical
 exact if hv: Cube.Guard (Pose.swing v b (x • z) G) e then fixed (m:=m) (B:=B) v b G (p.shrink w) (x • z) hv else fixed (m:=m) (B:=B) v b G (p.shrink w) 0 (by simpa  [zeroSwing] using p.shrink w)

private abbrev band (r:ℝ):= Metric.ball (0:ℝ) (r/deter)
-- if qualification of h on full parameter radius band
variable (G:Pane (CSide m B)){z:SU.group.Color}{T:Broc.Table m B}{c K:ℝ}
lemma payStep (w:d<e)(p:Cube.Guard G d)(r:ℝ)(h:0<r)(hr:∀ z':SU.group.Color,‖z'‖≤r→Cube.Guard (Pose.swing v b z' G) e)(s T:Broc.Table m B)(f:castleT m B v e→ℂ)
    (g:Pro (landX 8 K (Skye.ends v) e) s f c)(dT:1≤K)(q:‖z‖≤ r/2):∀ pz:Cube.Guard (Pose.swing v b z G) e,∀ u₀:Cube.Guard (Pose.swing v b 0 G) e,
    ‖f (fixed (m:=m) (B:=B) v b G (p.shrink w.le) z pz) - f (fixed (m:=m) (B:=B) v b G (p.shrink w.le) 0 u₀)‖ ≤ deter⁻¹ * c*‖z‖:=by
 intro pz u₀
 by_cases ht:z=0
 · subst z; simp
 have hv:=norm_pos_iff.mpr ht; let α:=deter
 let Y:SU.group.Color:= (α/‖z‖) • z
 have hα:0<α:=deter_pos
 have hy : ‖Y‖=α:=by unfold Y; rw [norm_smul,Real.norm_of_nonneg (by positivity),div_mul_cancel₀ _ hv.ne']
 let a:= ‖z‖/α; have ha:0<a:=div_pos hv hα
 have he:a • Y=z:=by unfold a Y; rw [smul_smul,show ‖z‖/α*(α/‖z‖)=1 by field_simp,one_smul]
 let B':=band r; have hB:a∈ B':=Metric.mem_ball.mpr (by rw [dist_zero_right]; exact (Real.norm_of_nonneg ha.le).le.trans_lt ( (div_lt_div_iff_of_pos_right hα).mpr (q.trans_lt (half_lt_self h))))
 have hz:(0:ℝ)∈ B':= Metric.mem_ball_self (div_pos h hα)
 have hR(x:ℝ)(hx:x∈ B'):‖x • Y‖≤ r:=by rw [norm_smul,hy]; exact (le_div_iff₀ hα).mp ((dist_zero_right ..).ge.trans (Metric.mem_ball.mp hx).le)
 let F:= cruise (m:=m) (B:=B) v b G w.le p Y (e:=e)
 have hf x (hx:x∈B'):F x= fixed (m:=m) (B:=B) v b G (p.shrink w.le) (x • Y) (hr _ (hR x hx)):= dif_pos _
 have hw : (landX 8 K (Skye.ends v) e).draw.test ℝ B' F:=by
    intro x hx i j
    let a(z):= SU.fund ((F z).val i j)
    let l(z:ℝ):= if i then SU.fund (Pose.swing v b (z • Y) G j) else SU.fund (G j)
    have hp : l=ᶠ[𝓝 x] a:=by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with x h; unfold a; rw [hf x h]; unfold fixed; cases i <;> rfl
    refine Allows.germ (f:=l) ?_ hp; cases i; exact allows_const _ ((fund_p _).le.trans dT); exact ((closeAngle Y hy.le G v b x 8 j)).mono dT
 have hm x (hx:x∈B'):=g.plot ℝ B' Metric.isOpen_ball F hw x hx
 have hd x (hx:x∈B') : DifferentiableAt ℝ (f ∘ F) x := (hm x hx).smooth.differentiableAt (by change ((↑(8:ℕ):WithTop ℕ∞)) ≠ 0; simp)
 have hp x (hx:x∈B') : ‖deriv (f ∘ F) x‖≤c := by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one] using (hm x hx).norm_le 1 (show 1 ≤ 8 by decide)
 have H:= Convex.norm_image_sub_le_of_norm_deriv_le hd hp (convex_ball ..) hz hB
 simp only [comp_apply,hf a hB,hf 0 hz, sub_zero, Real.norm_eq_abs, abs_of_pos ha] at H
 have HH:∀ (y x:SU.group.Color)(pa:Cube.Guard (Pose.swing v b y G) e)(l:Cube.Guard (Pose.swing v b x G) e)(t:y=x), fixed (m:=m) (B:=B) v b G (p.shrink w.le) y pa=fixed (m:=m) (B:=B) v b G (p.shrink w.le) x l:=by intro y x p l t; subst x; rfl
 have h₁:= HH _ _ (hr (a • Y) (hR a hB)) pz he; have h₂:= HH _ _ (hr (0 • Y) (hR 0 hz)) u₀ (zero_smul ℝ Y)
 refine (Eq.trans_le (congrArg₂ (fun A C:castleT m B v e=> ‖f A-f C‖) h₁.symm h₂.symm) H).trans_eq (by unfold a α; ring)
open Paige Hive

variable {L:Side}{j:ℕ}{o:Odd L.val}{Y:Paige.Pricing j L o (Vault.Thread j)} (P:Paige.Grasp Y B e)(W:Cascade.Interest (CSide m B))
    {T:∀ R,Lend m B e R}{price lot rate:ℝ}
local notation "S"=> Skye.ends v
local notation "TT"=>Pose.Test (CSide m B) d (r/2)
local notation "L0"=>Hive.drum
local notation "θ"=> Single (CSide m B)
-- exports smooth gateway on phase linked move of LP.1, exact nest and layout. 
structure VistaDelta (m B:Side){L:Side}{j:ℕ}{o:Odd L.val}{Y:Paige.Pricing j L o (Vault.Thread j)}{e:ℝ}(P:Paige.Grasp Y B e)(W:Cascade.Interest (CSide m B))(v:gaugeLink (CSide m B))(b:Bool)(d z fee rate C:ℝ)(I:Type) [Fintype I](Sg:I→ Finset (Seat (CSide m B)))(L₁:I→ List (Hake.Oboe (Single (CSide m B))))(X:I→Pose.Test (CSide m B) d z→ℂ)(G:I→ℝ):Prop where
 shape(i):Skye.ends v⊆ Sg i ∧ Branch.Grove (Tenant.terr _) (Sg i) ∧ Even (L₁ i).length ∧ ∀ t∈ L₁ i,Hive.home_n _ t.2∈ Sg i
 price(i):0≤ G i∧∀ x, ‖X i x‖ ≤ G i*‖x.2.val‖
 reads(i)(x y:Pose.Test (CSide m B) d z): Agrees (Sg i) x.1.val y.1.val→ x.2=y.2 →X i x=X i y
 cont(i):Continuous (X i)
 hire : ∑ i, Real.exp (rate*(Sg i).card)*fee^(L₁ i).length*G i ≤ C
 valuation(x:Pose.Test (CSide m B) d z): let U:= x.1.val; let V:=Pose.Products.after v b x;
    let T:= Hive.nest P W.P W.M;
    acts (1+∑ i,X i x • Hive.drum (L₁ i)) (T U)= T V
open Hive Branch Hake
private lemma end_g : Grove (terr _) S:=by rcases v with ⟨i,j⟩; unfold Skye.ends; exact Grove.join (y:=i+step j) (.single _) (mem_singleton_self _) (Lat.oneTouch ..)

lemma policy (v':Hive.Vista P W.M W.P T 8 K price lot rate)(w:d<e)(r:ℝ)(h:0<r)(hr:∀ x:Pane (CSide m B),Cube.Guard x d→∀ z':SU.group.Color,‖z'‖≤r→Cube.Guard (Pose.swing v b z' x) e)(dT:1≤K)(l:0≤price)(t:0≤rate)(p:0≤lot):
    ∃ (I:Type)(_ : Fintype I)(D:I → Finset (Seat (CSide m B)))(F:I → List (Oboe θ))(Γ:I → Pose.Test (CSide m B) d (r/2)→ℂ)(c:I → ℝ), VistaDelta m B P W v b d (r/2) price rate (deter⁻¹ * Real.exp (2*rate) * Real.exp (lot*2*price^2)) I D F Γ c:=by
  obtain ⟨hu,hx,pay⟩:= v'.carry S (end_g v)
  let I:= (T S).slots; letI:Fintype I:=Lend.holder (T S)
  let c:I→ Axx _ _ _ := (T S).crew
  let s0 (i:I):= (c i).1; let y (i:I) :=(c i).2.2.1; let Lg (i:I):=(c i).2.1; let H (i:I):=(c i).2.2.2
  let X1 (x: Pose.Test (CSide m B) d (r/2)):= fixed (m:=m) (B:=B) v b x.1.val (x.1.property.shrink w.le) x.2.val (hr _ x.1.property _ (x.2.property.trans (half_le_self h.le)))
  let X0 (x: Pose.Test (CSide m B) d (r/2)):= fixed (m:=m) (B:=B) v b x.1.val (x.1.property.shrink w.le) 0 (by rw [zeroSwing (m:=m) (B:=B)]; exact x.1.property.shrink w.le)
  have Xc : Continuous X1:=by
    let T₀:=Pose.Test (CSide m B) d (r/2); have ht: Continuous (fun x:T₀=>x.1.val) := continuous_subtype_val.comp continuous_fst; have hu: Continuous (fun x:T₀=> x.2.val):=continuous_subtype_val.comp continuous_snd; have hc:= (Pose.swingC v b).comp (hu.prodMk ht)
    refine Continuous.subtype_mk (continuous_pi fun i=> ?_) _; cases i; exact ht; exact hc
  have Xc' : Continuous X0:= by
    let T:=Pose.Test (CSide m B) d (r/2); refine Continuous.subtype_mk (continuous_pi fun i=> ?_) _; cases i; exact continuous_subtype_val.comp continuous_fst; change Continuous fun x:T=> Pose.swing v b 0 x.1.val; simp_rw [zeroSwing (m:=m) (B:=B)]; exact continuous_subtype_val.comp continuous_fst
  let W'(i:I):= (y i ∘ X1 - y i ∘ X0)
  let H'(i:I):= deter⁻¹*H i
  have Wp (i):= (hu i).2.2.2.2
  refine ⟨I,inferInstance,s0,Lg,W',H', {
      shape:=fun i=> ⟨(hu i).1,(hu i).2.1,(hu i).2.2.1,(hu i).2.2.2.1⟩
      price:=fun i=> ⟨mul_nonneg (inv_pos.mpr deter_pos).le (Wp i).pos,fun x=> payStep v b x.1.val w x.1.property r h (hr x.1.val x.1.property) (s0 i) (s0 i) (y i) (Wp i) dT x.2.property _ _⟩
      reads:=?_
      cont:=fun i=>( (Wp i).cont.comp Xc).sub ((Wp i).cont.comp Xc')
      hire:=?_
      valuation:=?_ }⟩
  · intro i x y h v'
    have hx(j:Bool):Agrees (s0 i) ((X1 x).val j) ((X1 y).val j):=by cases j; exact h; change Agrees _ (Pose.swing v b x.2.val _) _; rw [v']; exact Pose.swing_local v b _ h
    have hh(j:Bool):Agrees (s0 i) ((X0 x).val j) ((X0 y).val j):=by cases j; exact h; exact Pose.swing_local v b _ h
    exact congrArg₂ (fun x y:ℂ=>x-y) ((Wp i).reads (X1 x) (X1 y) hx) ((Wp i).reads (X0 x) (X0 y) hh)
  · have he :(Skye.ends v).card≤ 2:=by unfold Skye.ends; exact (card_insert_le ..).trans (by simp)
    let E:= deter⁻¹*Real.exp (2*rate); have hE:0≤E:=mul_nonneg (inv_pos.mpr deter_pos).le (Real.exp_pos _).le
    refine le_trans ?_ (show E * (∑ i:I, Hive.hireC rate price S (c i)) ≤ _ from mul_le_mul_of_nonneg_left (hx.trans (Real.exp_monotone (by gcongr; exact_mod_cast he))) hE)
    rw [mul_sum]; apply sum_le_sum; intro i _; let A:= s0 i; have hvZ:= Finset.card_sdiff_add_card_eq_card (s:=S) (t:=A) ((hu i).1) -- check signature
    have h1:((A.card:ℕ):ℝ)≤2+((A \ S).card:ℝ):=by exact_mod_cast (show A.card ≤2+(A \ S).card by omega)
    have hl:0≤ H i:=(Wp _).pos; unfold H'; apply le_trans (b:= (Real.exp (rate*(A \ S).card)*Real.exp (2*rate)) * price^(Lg i).length * (deter⁻¹*H i)) _ (Eq.le ?_); swap; · unfold E A Hive.hireC Acorn.cost Branch.rent s0 Lg H; ring
    apply mul_le_mul_of_nonneg_right _ (by have he:=deter_pos; positivity); apply mul_le_mul_of_nonneg_right _ (by positivity); rw [←Real.exp_add]; exact Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_left h1 t])
  intro x U V T'
  have hp:= pay (X0 x); have hg:= pay (X1 x)
  change acts _ (T' U)=T' (Pose.swing v b 0 U) at hp; rw [zeroSwing (m:=m) (B:=B)] at hp
  change acts _ (T' U)=T' V at hg
  simp only [W',Pi.sub_apply,comp_apply,sub_smul,Finset.sum_sub_distrib]
  rw [act_add,act_one,act_sub]; change T' U + ((acts _) _- (acts _) _)=_
  change T' U+(acts (∑ j:I,Hive.vowC (c j) (X1 x)) (T' U)-acts (∑ j:I,Hive.vowC (c j) (X0 x)) (T' U))=T' V; rw [hp,hg]; abel
end PureForce.Vessel
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
