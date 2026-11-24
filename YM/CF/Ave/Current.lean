import YM.CF.Ave.Pass

/-! The extensive real flight invoice uses uniformly local cylinder densities. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Filter Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e H a K : ℝ}
def moneyW (m B : Side) (e : ℝ) : Lodge (Index m) ℂ (Briar m B e) (Court m B) where
  fare:=norm
  pick:=routeS (m:=m) (B:=B)
  zone S U V:= Agrees (mount m B S) U.val V.val
  grows g h:= fun _ u k=> h _ (mount_up g u) (mount_up g k)
  store _:= ⊤
  stair _:= le_rfl
  wallL _:= isClosed_univ -- tune
  free:= norm_zero
  single:=norm_one
  normF _:=le_rfl
  plus:=norm_add_le
  scale x c:=norm_smul ..
  times x y:=(norm_mul ..).le
  sound:=continuous_norm
  rule _:= AlgHom.id ℝ ℂ
  ct _:= continuous_id
def Treasury (m B : Side) (e:ℝ) : Petal.Cabin cloud (moneyW m B e) where
  seat U:= rock m B U.val
  unionV:= partner m B
  board g:= (pass m B g).measurableEmbedding
  plenty g:= rain_g m B g
  mass g U x:= by change law m B (Lattice.gauge g U.val) _=law m B U.val x; exact law_g m B U.val x g
  ct:= (travel m B e 1 le_rfl).ct
  reflL _ _:=fun _ _ _=>rfl
def cin (m B : Side) (f : Post m B→ℂ) (x:Train m B e):=accessK m B (stick 0) (stick 0) none x.1.val (slot m x.2) f
lemma cin_paid {f : Post m B→ℂ} {S : Stamp m B} (p:Eck m B S K f) (b : Room B e) : Manifest (Treasury m B e) (cin m B f) K (pavilion m B S) (chairs m B S) := by
  have ht x (k:x∈ booth (Treasury m B e)) : TenantK (stayX x) := tenant_t b k
  refine ⟨p.posT,chair_pad,fun x k=>?_,fun _ _=>Algebra.mem_top, ?_,fun x=> nested_ch S,?_, (fun k i l=>scents (e:=e) (S:=S) (show (1:ℝ) ≤ 1 from le_rfl) (show (welter m B e 1 le_rfl).zone (pavilion m B S) _ _ from k) _ l), fun g x k=>?_⟩
  · unfold cin; rw [entrance (p:=stick 0) (q:=stick 0) (m:=m) (B:=B) (v:=none) (ht x k)]; exact p.norms _
  · let A := banner m B e {0}; let F := fun t:FlagU m B=> accessK m B (stick 0) (stick 0) none t.1 t.2 f
    have he : stick (0:Row)∈zone {0} := stick_in _ (mem_singleton_self _)
    have h : ContinuousOn F A := access_cont A _ _ _ f p.continuousE (fun t p=> drives b p.1 p.2 he he (by rw [sub_self,norm_zero]; positivity) none) (dress _ _ _ he he none b)
    let G := fun p:Train m B e=>(p.1.val,slot m p.2); refine h.comp (f:=G) ((continuous_subtype_val.comp continuous_fst).prodMk ((slot_cont m).comp continuous_snd)).continuousOn (fun p u=>pays (m:=m) (B:=B) (e:=e) (v:=p) (show p∈Breath m B e from u))
  · intro x y g l P v; change Agrees (mount m B (pavilion m B S)) x.1.val y.1.val at P; rw [mount_p] at P; exact access_eq S p none trivial (ht _ g) (ht _ l) P (fun i l=> v i.1 (mem_product.mp l).1)
  · symm; exact exact_station f (stick 0) (stick 0) none x.1.val (slot m x.2) g (ht _ k) (fun x g=>p.gauge g x)
lemma adjEn : Hon weave weave (fun z x=> Kmat z x*Pmat z x) := launchH.join (Tour.Enters.site amp launchH attends)
structure Intensive (e : ℝ) (c : Foot m B) (u K : ℝ) : Prop where
  paysT : ∃ F w, Charge (moneyW m B e) (terr _) u K F w ∧ ∀ x, energ m B c x.val=∑ S:Acres m,F S x -- tune infer
lemma codify_hit (m B : Side) (C : Stamp m B→ℝ) (x : Index m) (u : ℝ) : hitE u (fun S=>∑ i∈dest (pavilion m B) S,C i) x=cellHit m B u C x := by
  unfold hitE hit0 cellHit spotHit dest; simp_rw [sum_filter]
  -- pull the mask sum and restore specific site incidence
  conv_lhs =>
    arg 2; ext i
    rw [mul_sum,ite_sum_zero]
  rw [sum_comm]; refine sum_congr rfl ?_; intro S _; rw [sum_eq_single_of_mem _ (mem_univ (pavilion m B S))]; simp; intro i _ g; simp [Ne.symm g]
lemma thermal {u : ℝ} (p:0<u) : ∃ J:ℕ,∀ B : Side,J≤B.val → ∃ K:ℝ,0≤K ∧ ∀ e:ℝ, Room B e → ∀ m c, Intensive (m:=m) (B:=B) e c u K := by
  have he := tours _ amp adjEn; obtain ⟨a,K,hA,g,U⟩:= he; obtain ⟨J,h⟩:=exists_nat_gt (u*21^4/a)
  refine ⟨J,?_⟩; intro B k
  let L := Real.exp (u*21^4)*(16*(7*(B.val:ℝ)+1)^4*K); refine ⟨L,by unfold L; positivity,?_⟩; intro e b m c
  let z := codify (m:=m) (B:=B) c; obtain ⟨F,C,H,P⟩:= U z
  have hc : ∀ S:Stamp m B,Manifest (Treasury m B e) (cin m B (F S)) (C S) (pavilion m B S) (chairs m B S) := fun S=>cin_paid (H.stamped S) b
  let D : Stamp m B→ Briar m B e→ℂ := fun S=>motor (Treasury m B e) (cin m B (F S))
  let T := pavilion m B
  have ht S : Token (moneyW m B e) (T S) (D S) (C S) (Grove (terr _)) := { (hc S).flush with shape := fun c=> pad_grove (m:=m) (B:=B) ((show Eck m B S (C S) _ from H.stamped S).conduct c) }
  have hv (x:Briar m B e) : ∑ S:Stamp m B,D S x=energ m B c x.val := by
    have he z' (v' : (x,z')∈Breath m B e) : ∑ S:Stamp m B, cin m B (F S) (x,z')=energ m B c x.val := by
      let y : Train m B e:= (x,z'); have hx := tenant_t b v'
      unfold cin; simp_rw [entrance (p:=stick 0) (q:=stick 0) (m:=m) (B:=B) (v:=none) hx]; exact (P (⟨_,hx⟩:Post m B)).symm
    change ∑ S:Stamp m B, (∫ i, law m B x.val i • cin m B (F S) (x,i) ∂rains m)=energ m B c x.val
    rw [←integral_finsetSum]; swap
    · intro i hi; exact net_compact (show Continuous (fun z=>law m B x.val z • cin m B (F i) ((x,z):Train m B e)) from (hc i).cashG x)
    simp_rw [←smul_sum]; let G:= energ m B c x.val
    calc
      _ = ∫ i, law m B x.val i • G ∂rains m := by
        apply integral_congr_ae; apply Eventually.of_forall; intro i
        by_cases g:law m B x.val i=0
        · exact (show law m B x.val i • (∑ S:Stamp m B,cin m B (F S) ((x,i):Train m B e))= law m B x.val i • G from by rw [g]; exact (zero_smul ..).trans (zero_smul ..).symm)
        exact congrArg (fun v:ℂ=>law m B x.val i • v) (he i (show (x,i)∈Breath m B e from g))
      _ = G := by rw [integral_smul_const,rain_law,one_smul]
  let V (S:Acres m) := dest T S; let w (S:Acres m) := ∑ i∈V S, C i
  have hh : u*21^4 ≤ a*(B.val:ℝ) := (le_of_lt ((div_lt_iff₀ hA).mp h)).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast k) hA.le)
  refine ⟨_,w,⟨fun S=> Token.mass (V S) D (fun i=> C i) (fun i l=>by rw [←show T i=S from (mem_filter.mp l).2]; exact ht i), fun x=>?_⟩,fun x=>by rw [←hv]; exact lump T (fun S=>D S x)⟩ -- tuning order
  rw [show hitE u w x=cellHit m B u C x from ?_]; swap
  · exact codify_hit _ _ (show Stamp m B→ℝ from C) _ _
  exact hit_transfer p.le hh (fun S c=> (show Eck m B S _ _ from H.stamped S).conduct c) (fun S=>(ht S).price) (fun i=> H.payline i) g.le x
-- scalar costs and Cloud estimate
variable {u : ℝ} {p : 1 ≤ H} {w : Acres m→ℝ} {F : Acres m→Briar m B e→ Ewe m B} (l : Charge (welter m B e H p) (terr _) u a F w)
include l
lemma gradeZero : Charge (moneyW m B e) (terr _) u a (fun S x=>pane (F S x)) w := by
  refine ⟨fun S=>?_,l.rankV⟩; have g:= l.pledge S
  refine ⟨g.price,g.shape,fun _=> Algebra.mem_top,fun v=>congrArg (fun x:Ewe m B=>pane x) (g.locality v),fun x=>(pane_cost H (zero_le_one.trans p)).trans (g.owns x), ?_,fun h x=>?_⟩ -- tune
  · exact ((panHom (Hearth m B)).toLinearMap.continuous_of_finiteDimensional).comp g.ct
  change pane (F S x)=pane (F S ((welter m B e H p).pick h x)); rw [← g.dress]; exact (center_b _ _).symm
omit l
lemma realFlight (e' : Room B e) (x : Briar m B e) (c : Foot m B) : star (energ m B c x.val)=energ m B c x.val := by
  have he := wiel_ok c e' x.property
  have hj := he.projection
  unfold energ; rw [←Matrix.trace_conjTranspose]; change Matrix.trace (star _)=_; rw [star_mul, show star (lens m B c x.val) = _ from hj.2, show star (wiel m B c x.val)=_ from he.self]; exact Matrix.trace_mul_comm .. -- tune cc
lemma pirates (t : ℝ) (s : 1≤H) (p : 0<t) (g : t ≤ 1) (q : 1≤H/t) (l : Charge (welter m B e (H/t) q) (terr _) u a F w) : Charge (welter m B e H s) (terr _) u (t*a) (fun S x=> cloudless (F S x)) (fun S=> t*w S) := by
  refine ⟨fun S=>?_,fun x=>?_⟩
  · have h := l.pledge S; refine ⟨mul_nonneg p.le h.price,fun l=> h.shape (right_ne_zero_of_mul l),fun x=>?_,fun k=>?_,fun x=>?_, (convCloud (n:=Hearth m B)).comp h.ct,fun i x=>?_⟩
    · exact cloudClose _ _ (h.gram x)
    · exact congrArg _ (h.locality k)
    · exact (cloudy_cost (n:=Hearth m B) _ H t s p g).trans (mul_le_mul_of_nonneg_left (h.owns x) p.le)
    change Pastry.fold _ _=cloudless (F S ((welter m B e (H/t) q).pick i x)); rw [←h.dress]; exact cloudT ..
  unfold hitE; simp_rw [mul_left_comm _ t, ←mul_sum]; exact mul_le_mul_of_nonneg_left (l.rankV x) p.le
end YM.CF.Ave
