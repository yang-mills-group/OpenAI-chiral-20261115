import YM.SU5.FiniteGaugeData.Tower.Accord
import YM.SU5.Selected.Seats
/-! # Riemann smearing approximates projection, even with discontinuous shifts.
Actual average over offsets, limit one-sided offsets of fixed width then send width to zero.
No choice or assumption of a Borel representation, no claim allowing diagonal regime. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy Vacancy.Average Finset
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H : Hilbert} (M : Mesh) (P : Players (marks M) H)
local notation "I" r:max=> Fin (M.L^r)
local notation "U" v:max x:max=> P.play (notch M v (x:ℤ))
local notation "S" q:max m:max=> Average.center (fun i:I m=> (U q (i.val:ℤ))) -- on H.Op too
local notation "T" q:max m:max=> Average.center (fun i:I m=> (P.play (-(notch M q (i.val:ℤ)))))
lemma avg_fin {Y: Type*} [NormedAddCommGroup Y][NormedSpace ℂ Y] (f:ℕ→Y) (q:ℕ) : (q:ℂ)⁻¹ • ∑ i∈Finset.range q,f i= Average.center (fun i:Fin q=> f i.val):=by
 unfold Average.center; rw [Fintype.card_fin,← Fin.sum_univ_eq_sum_range]
noncomputable def average (r k:ℕ) : H.Op:= (S r k)
noncomputable def returnavg (r k:ℕ) : H.Op:= (T r k)
lemma avg_num (t : ℕ) : 0 < M.L^t:=pow_pos (lt_of_lt_of_le (by decide) M.Llarge) t
lemma avg_lives (t :ℕ) : Nonempty (Fin (M.L^t)) := ⟨⟨0,avg_num M _⟩⟩
local notation "F" n:max t:max=> average M P (n+t) t -- gives interval width Δ_n
lemma avgvalue (r k:ℕ)(x:H): average M P r k x= Average.center (fun i:Fin (M.L^k)=> (U r (i.val:ℤ)) x):= (natural (fun i:Fin (M.L^k)=> U r (i.val:ℤ)) (ContinuousLinearMap.apply ℂ H.space x)).symm
lemma avgback (r k:ℕ)(x:H): returnavg M P r k x= Average.center (fun i:Fin (M.L^k)=> (P.play (- notch M r (i.val:ℤ))) x):= (natural (fun i:Fin (M.L^k)=> P.play (- notch M r (i.val:ℤ))) (ContinuousLinearMap.apply ℂ H.space x)).symm
lemma avg_balance (r k:ℕ) : (average M P r k).adjoint=returnavg M P r k:= by
 change star (average M P r k) = _; unfold average returnavg Average.center; simp_rw [star_smul,star_inv₀,star_natCast,star_sum]; exact congrArg (_ • ·) (Finset.sum_congr rfl fun i _=> P.neg_adjoint _)
lemma avg_commute (r k :ℕ) (x : marks M): (average M P r k).comp (P.play x)=(P.play x).comp (average M P r k):=by
 ext1 y
 simp only [ContinuousLinearMap.comp_apply,avgvalue,← Vacancy.Average.natural, P.symmetric H x]
lemma avg_cost (r k:ℕ) (x:H) : ‖average M P r k x‖ ≤ ‖x‖ := by
 haveI := avg_lives M k; rw [avgvalue]; exact Average.norm_worth fun i=> P.pulls ..

lemma pay_chosen (r k :ℕ) (x:H) : average M P r k x=birkhoffAverage ℂ (U r 1) _root_.id (M.L^k) x:=by
 let G:= (U r 1); have hv(n:ℕ):(⇑G)^[n] x=(U r (n:ℤ)) x:=by
    induction n with
    | zero=>rw [Nat.cast_zero,notch_zero,P.play_zero]; rfl
    | succ n h=>rw [Function.iterate_succ_apply',h]; unfold G; rw [P.paved,Nat.cast_add_one,notch_add,add_comm _ (notch ..)]
 rw [avgvalue,← avg_fin (fun n:ℕ=> (U r (n:ℤ)) x)]; unfold birkhoffAverage birkhoffSum; unfold G at hv; simp_rw [hv]; rfl
lemma slide_unit (r k :ℕ) (x:H) : dist ((U r 1) (average M P r k x)) (average M P r k x) ≤ 2*‖x‖/(↑(M.L^k:ℕ):ℝ):=by
 rw [← ContinuousLinearMap.comp_apply,← avg_commute,ContinuousLinearMap.comp_apply,pay_chosen,pay_chosen,dist_birkhoffAverage_apply_birkhoffAverage]
 let n:=M.L^k; let G:= (U r 1); change dist ((⇑G)^[n] x) x/_ ≤_; refine div_le_div_of_nonneg_right ?_ (by positivity)
 have he(n:ℕ):‖(⇑G)^[n] x‖=‖x‖:=by induction n with | zero=>rfl | succ n h=>rw [Function.iterate_succ_apply',show ∀ t,G t=P.play (notch M r 1) t from fun _=>rfl, P.wins,h] -- `rw` rewrites G inside iter too? simp?
 rw [dist_eq_norm,two_mul]; exact (norm_sub_le ..).trans_eq (by rw [he])
lemma slides (r k l:ℕ) (x:H) : dist ((U r (l:ℤ)) (average M P r k x)) (average M P r k x) ≤ (l:ℝ)*(2*‖x‖/(↑(M.L^k:ℕ):ℝ)):=by
 let y:=average M P r k x; induction l with
 | zero=> rw [Nat.cast_zero,notch_zero,P.play_zero]; simp
 | succ n ih=>
    rw [Nat.cast_add_one,Nat.cast_add_one,add_mul,one_mul,notch_add,add_comm _ (notch M r 1), ← P.piles,ContinuousLinearMap.comp_apply]
    refine (dist_triangle _ ((U r 1) y) _).trans (add_le_add ?_ (slide_unit M P r k _))
    rw [P.rigid H]; exact ih
lemma slidesBack (r k l:ℕ)(x:H) : dist (P.play (-notch M r (l:ℤ)) (average M P r k x)) (average M P r k x) ≤ (l:ℝ)*(2*‖x‖/(↑(M.L^k:ℕ):ℝ)):=by
 let y:= average M P r k x; rw [←P.rigid H (notch M r (l:ℤ)),P.paved,add_neg_cancel,P.play_zero,ContinuousLinearMap.id_apply,dist_comm,dist_comm]; exact (le_trans (le_of_eq (dist_comm ..)) (slides M P r k l x)) -- tune sw

-- divisibility of grid, split coarse tiles. n+b represents same from r (notch actual)
lemma transmit (n t b:ℕ) (i:ℕ) (j:ℕ) : notch M (n+t) (i:ℤ)+notch M (n+(t+b)) (j:ℤ)= notch M (n+(t+b)) ((j+ M.L^b*i:ℕ):ℤ):=by
 rw [← notch_up M (n+t) (n+(t+b)) (by omega) i,←notch_add]; unfold castor; push_cast; rw [show (n+(t+b))-(n+t)=b from by omega,add_comm _ (↑j:ℤ)]
lemma subdivide (n t b:ℕ) : F n (t+b)=(average M P (n+(t+b)) b).comp (F n t):=by
 let r:= M.L^t; let k:= M.L^b; let e: Fin r×Fin k ≃ Fin (M.L^(t+b)):= finProdFinEquiv.trans (finCongr (pow_add ..).symm)
 ext1 x
 let W(i:Fin (M.L^(t+b))):H:= (U (n+(t+b)) (i.val:ℤ)) x
 rw [avgvalue M P (n+(t+b)) (t+b),show Average.center _= Average.center (fun i:Fin r×Fin k=> W (e i)) from (Average.trade e W).symm, domino, fubini, ContinuousLinearMap.comp_apply, avgvalue, avgvalue]
 simp only [← Vacancy.Average.natural]
 refine congrArg Average.center (funext fun j=> congrArg Average.center (funext fun i=>?_))
 change W (e (i,j))=(P.play _) (P.play _ x)
 rw [P.paved,add_comm _ (notch M (n+t) _),transmit]; rfl
lemma regimen (r t b:ℕ)(x:H):
    let s:= r+(t+b); let a:= (F r (t+b)) x -- macro parse! parentheses
    dist ((returnavg M P s b) a) a ≤ (2*‖x‖)/(↑(M.L^t:ℕ):ℝ):=by
 intro s a
 rw [avgback]; haveI := avg_lives M b; apply le_trans _ (le_refl _)
 nth_rw 2 [← Average.constant (A:=I b) a]; -- tactic
 apply Average.norm_dist; intro i
 have h : (i.val:ℝ) ≤ (M.L:ℝ)^b:= by exact_mod_cast i.isLt.le
 apply (slidesBack M P s (t+b) _ x).trans; push_cast; refine (mul_le_mul_of_nonneg_right h (by positivity)).trans_eq ?_; rw [pow_add]; field_simp [show (M.L:ℝ) ≠ 0 from (Nat.cast_ne_zero.mpr (by have hx:=M.Llarge; omega))] -- tune

lemma inquest (n:ℕ) (x:H): CauchySeq (fun i:ℕ=> (F n i) x):=by
 let d(i:ℕ):H:= (F n i) x; let a i:= ‖d i‖^2
 have he: Antitone a:= by
    intro i j h; obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le h
    unfold a d; rw [subdivide,ContinuousLinearMap.comp_apply]; exact pow_le_pow_left₀ (norm_nonneg _) (avg_cost ..) _
 let c:= ⨅ i:ℕ,a i; have hc:BddBelow (Set.range a):=by use 0; rintro _ ⟨i,rfl⟩; exact sq_nonneg _
 have ht:Tendsto a atTop (𝓝 c):=tendsto_atTop_ciInf he hc
 let L:= ‖x‖; let u(j:ℕ):= (2*L)/(↑(M.L^j:ℕ):ℝ); have hu:Tendsto u atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<M.L from lt_of_lt_of_le (by norm_num) M.Llarge)))
 apply Metric.cauchySeq_iff'.mpr; intro ε e
 let ρ:= ε^2/4; have hr:0<ρ:=by unfold ρ; positivity
 have hz:Tendsto (fun i=>u i*L) atTop (𝓝 0):=by simpa using hu.mul_const L
 obtain ⟨j,i,jh⟩:= ((ht.eventually (gt_mem_nhds (lt_add_of_pos_right c hr))).and (hz.eventually (gt_mem_nhds hr))).exists -- gt_mem instead
 refine ⟨j,?_⟩
 intro k h; obtain ⟨b,rfl⟩:= Nat.exists_eq_add_of_le h
 let r:=j+b; let t:=n+(j+b); let G:= average M P t b
 have hE: d r= G (d j):=by unfold r d; rw [subdivide]; rfl
 let E:=inner ℂ (d r) (d j); let K:=G.adjoint
 have ht : inner ℂ (d r) (d r)=inner ℂ (K (d r)) (d j):= by nth_rw 2 [hE]; rw [ContinuousLinearMap.adjoint_inner_left]
 have hπ := norm_inner_le_norm (𝕜:=ℂ) (K (d r) - d r) (d j)
 rw [inner_sub_left, ← ht] at hπ
 have hq : ‖K (d r) - d r‖ ≤ u j := by rw [←dist_eq_norm]; unfold K G; rw [avg_balance]; exact regimen M P n j b x
 have hp:0 ≤ u j:=by unfold u L; positivity
 change (u j)*L < ρ at jh
 have h' : ‖inner ℂ (d r) (d r)- E‖ < ρ := hπ.trans_lt (lt_of_le_of_lt (mul_le_mul hq (avg_cost ..) (norm_nonneg _) hp) jh)
 have h'' := (Complex.re_le_norm _).trans h'.le; rw [Complex.sub_re] at h''; change RCLike.re (inner ℂ (d r) (d r))- RCLike.re (inner ℂ (d r) (d j))≤_ at h''
 rw [inner_self_eq_norm_sq] at h''
 have hx : c≤ a r:= ciInf_le hc _
 change dist (d _) (d _) < ε; apply (sq_lt_sq₀ dist_nonneg e.le).mp; rw [dist_eq_norm,norm_sub_sq (𝕜:=ℂ)]; change a r-2*_+a j < _; change a r-_ ≤ _ at h''; change a j<c+ ρ at i; unfold ρ at *; unfold r at *; linarith
lemma smear_exists (n:ℕ) (x:H):∃ y:H,Tendsto (fun i:ℕ=> (F n i) x) atTop (𝓝 y):= cauchySeq_tendsto_of_complete (inquest M P n x)
noncomputable def smoother (n:ℕ) (x:H):H:=(smear_exists M P n x).choose
local notation "R" q:max=> smoother M P q
lemma smears (n:ℕ)(x:H): Tendsto (fun i:ℕ=> (F n i) x) atTop (𝓝 ((R n) x)) := (smear_exists M P n x).choose_spec
lemma merit (n:ℕ)(x:H): ‖(R n) x‖≤ ‖x‖:= le_of_tendsto ((smears M P n x).norm) (Eventually.of_forall fun i=> avg_cost ..)
noncomputable def roller (n:ℕ):H.Op := LinearMap.mkContinuous (show H→ₗ[ℂ] H from {
 toFun := smoother M P n
 map_add' x y:= tendsto_nhds_unique (smears M P n (x+y)) (by simp_rw [map_add]; exact (smears M P n x).add (smears M P n y))
 map_smul' v x:= by apply (tendsto_nhds_unique (smears M P n (v • x))); simp_rw [map_smul]; exact tendsto_const_nhds.smul (smears M P n x) }) 1 (fun x=>by rw [one_mul]; exact merit M P n x)
lemma rolls (n:ℕ)(x:H): Tendsto (fun i:ℕ=> (F n i) x) atTop (𝓝 (roller M P n x)) := smears M P n x
lemma slipper (n : ℕ) (x:H) (k v:ℕ) : ∀ (l:ℕ)(h: k≤ n+l),
    let i := notch M k (v:ℤ); let c:= mill M n
    dist (P.play i ((F n l) x)) ((F n l) x) ≤ (2*‖x‖/(c:ℝ)) * i.val ∧
    dist (P.play (-i) ((F n l) x)) ((F n l) x) ≤ (2*‖x‖/(c:ℝ)) * i.val:=by
 intro l h; let t:=n+l; let a:=M.L^(t-k)*v
 have z: notch M t (a:ℤ)=notch M k (v:ℤ):=by unfold a; rw [Nat.cast_mul,Nat.cast_pow]; exact notch_up M k t h (v:ℤ) -- mismatch castor
 intro i c; change _; have he: 0 < (mill M t:ℝ):=mill_pos ..; have hp:0 < (mill M n:ℝ):=mill_pos ..
 have hX: ((M.L:ℝ)^l*(mill M t:ℝ))=(mill M n:ℝ):=by
    have ht:= mill_finer M n (n+l) (by omega); rw [show n+l-n=l by omega] at ht; simpa using congrArg NNReal.toReal ht
 have hu : (2*‖x‖/(c:ℝ))*i.val = (a:ℝ)*(2*‖x‖/(↑(M.L^l:ℕ):ℝ)) := by
    unfold i; rw [← z]; change _ * bell M t (a:ℤ)=_; unfold c bell; rw [Int.cast_natCast,Nat.cast_pow]; have hP : 0 < (M.L:ℝ):= by exact_mod_cast lt_of_lt_of_le (by decide) M.Llarge
    field_simp; rw [←hX]; ring!
 rw [hu]; unfold i; rw [← z]; exact ⟨slides ..,slidesBack ..⟩
lemma stride (n : ℕ) (x:H) (l:marks M) : dist (P.play l ((R n) x)) ((R n) x) ≤ (2*‖x‖/(mill M n:ℝ)) * |l.val| := by
 have he (l: marks M): Tendsto (fun i:ℕ=>dist (P.play l ((F n i) x)) ((F n i) x)) atTop (𝓝 (dist (P.play l ((R n) x)) ((R n) x))) := (((P.play l).continuous.continuousAt.tendsto.comp (smears M P n x)).dist (smears M P n x))
 apply le_of_tendsto (he l)
 obtain ⟨k,j,rfl⟩:= notch_exists M l
 filter_upwards [eventually_ge_atTop k] with l h
 rcases Int.eq_nat_or_neg j with ⟨j,rfl|rfl⟩ -- check lemma name
 · refine (slipper M P n x k j l (by omega)).1.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
 rw [show notch M k (-(j:ℤ))= - notch M k (j:ℤ) from ?_, AddSubgroup.coe_neg, abs_neg]; refine (slipper M P n x k j l (by omega)).2.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
 apply Subtype.ext; change bell M k (-(j:ℤ)) = - bell M k (j:ℤ); simp [bell]
lemma roll_lives (n : ℕ)(x:H): roller M P n x∈ P.lives H:= by
  rw [P.living]; intro ε e
  let c:=2*‖x‖/(mill M n:ℝ); have h:0≤c:=by unfold c; positivity
  refine ⟨ε/(c+1),by positivity,?_⟩
  intro i hi; refine (stride M P n x i).trans_lt (lt_of_le_of_lt ?_ ((lt_div_iff₀ (by positivity : 0<c+1)).1 hi)); nlinarith [abs_nonneg (i:ℝ)]
lemma center_base (n t:ℕ) : (F n t).comp P.pi_c=P.pi_c.comp (F n t):= P.commutes_c _ (fun _=> (avg_commute M P _ _ _).symm)
lemma clear_course (n:ℕ)(x:H) : roller M P n (P.pi_c x)=roller M P n x:= by
  rw [← P.pi_fixer (roll_lives M P n x)]
  apply tendsto_nhds_unique (rolls M P n (P.pi_c x)); simp_rw [← ContinuousLinearMap.comp_apply,center_base,ContinuousLinearMap.comp_apply]
  exact P.pi_c.continuous.continuousAt.tendsto.comp (rolls M P n x)
lemma rollers (x:H): Tendsto (fun i=> roller M P i x) atTop (𝓝 (P.pi_c x)):=by
 refine Metric.tendsto_nhds.mpr ?_; intro ε e; let y:= P.pi_c x; obtain ⟨δ,h,t⟩:= P.living.mp (P.repaired x) (ε/2) (half_pos e)
 have hv:Tendsto (fun i:ℕ=> (mill M i:ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.mpr (vanishes M)
 filter_upwards [hv.eventually (gt_mem_nhds h)] with i hi
 have hq (r:ℕ)(q:Fin (M.L^r)): dist ((U (i+r) (q.val:ℤ)) y) y ≤ ε/2:=by
    apply (t (notch M (i+r) (q.val:ℤ)) _).le
    change |bell M (i+r) (q.val:ℤ)| < _; rw [natural_time, abs_of_nonneg (whenly M (i+r) q.val).property]
    have hx: whenly M (i+r) (M.L^r)=mill M i:=by
       rw [whenly,Nat.cast_pow]; have p:= mill_finer M i (i+r) (by omega); rwa [show i+r-i=r by omega] at p
    apply lt_of_le_of_lt (show _ ≤ (mill M i:ℝ) from NNReal.coe_le_coe.mpr (((when_le M _ _ _).mpr q.isLt.le).trans_eq hx)) hi
 have hp (r:ℕ) : dist ((F i r) y) y ≤ ε/2:=by
    rw [avgvalue]; haveI:= avg_lives M r; nth_rw 2 [←Average.constant (A:=I r) y]; exact Average.norm_dist (hq r)
 rw [← clear_course M P i x]; exact (le_of_tendsto ((rolls M P i y).dist tendsto_const_nhds) (Eventually.of_forall hp)).trans_lt (half_lt_self e)
namespace Rides
variable {U₀:Type*} (Q : Alliance U₀ (marks M) H) (l : List U₀)
local notation "U₁" i:max=> Q.crew i
noncomputable def first (s t:ℕ):H.Op:= l.foldr (fun i a=> (average M (U₁ i) (s+t) t).comp a) (ContinuousLinearMap.id ℂ _)
noncomputable def camp (s:ℕ):H.Op:= l.foldr (fun i a=> (roller M (U₁ i) s).comp a) (ContinuousLinearMap.id ℂ _)
lemma first_step (s t:ℕ)(i:U₀) : first M Q (i::l) s t=(average M (U₁ i) (s+t) t).comp (first M Q l s t):=rfl
lemma camp_step (s:ℕ)(i:U₀) : camp M Q (i::l) s=(roller M (U₁ i) s).comp (camp M Q l s):=rfl
lemma motion (f : ℕ → H.Op) (y:H) (p : ∀ i (x:H), ‖f i x‖ ≤ ‖x‖) {x : ℕ→ H}{z:H}(t : Tendsto x atTop (𝓝 z))(u : Tendsto (fun i => f i z) atTop (𝓝 y)) : Tendsto (fun i=> f i (x i)) atTop (𝓝 y):=by
  apply tendsto_of_tendsto_of_dist u
  apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ ((tendsto_iff_dist_tendsto_zero.mp t))
  apply Eventually.of_forall; intro i; simp only [dist_eq_norm, ←map_sub]; exact (p i (z-x i)).trans_eq (norm_sub_rev ..) -- dist order
lemma consec (x:H)(s:ℕ): Tendsto (fun i=> first M Q l s i x) atTop (𝓝 (camp M Q l s x)):=by
 induction l with
 | nil=> exact tendsto_const_nhds
 | cons i l ih=> exact motion (fun j=>average M (U₁ i) (s+j) j) (roller M (U₁ i) s (camp M Q l s x)) (fun i _=> avg_cost ..) ih (rolls M (U₁ i) s _)
lemma onwards (x:H) : Tendsto (fun s=> camp M Q l s x) atTop (𝓝 (Q.stackS l x)):=by
 induction l with
 | nil=> exact tendsto_const_nhds
 | cons i l ih=> exact motion (roller M (U₁ i)) (((U₁ i).pi_c) (Q.stackS l x)) (fun i _=>merit ..) ih (rollers M (U₁ i) _)
lemma first_cost (x:H)(s t:ℕ): ‖first M Q l s t x‖ ≤ ‖x‖:=by
  induction l with
  | nil=> exact le_refl _
  | cons i l ih=> exact le_trans (avg_cost M (U₁ i) (s+t) t (first M Q l s t x)) ih
lemma camp_cost (x:H)(s:ℕ): ‖camp M Q l s x‖ ≤ ‖x‖:=le_of_tendsto ((consec M Q l x s).norm) (Eventually.of_forall fun i=>first_cost M Q l x s i)
end Rides
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.regimen

#print axioms YM.SelectionAnalysis.clear_course
#print axioms YM.SelectionAnalysis.rollers

#print axioms YM.SelectionAnalysis.Rides.onwards
