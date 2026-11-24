import YM.SU5.FiniteGaugeData.Pannier.Exacts
/-! # strengthening `wisps_budget`. Reusing the construction notes from Exacts (private) with same types. No cameo term even at fixed supplied ribbon K. *Paid per flake*. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Pannier.Damask
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
open RG
private lemma leafRow (U:Pane N)(x:Seat N)(t: x∉ Lattice.halo r (flags v U))(e:r ≤ (More N).val) (w:v≥0)(s:0≤a) : RayPrice U x (v+2*Real.exp (-(a*r))) a:=by
 intro j
 let A:= (v+2*Real.exp (-(a*r)))
 have he(j:Pec.Ok N)(h:r ≤ Font.dial x j) : ‖silt x j U‖ ≤ A*Real.exp (a*Font.dial x j):=by
    apply (group.curvature_norm _).trans; apply (group.chord_le_two _) |>.trans; unfold A; rw [add_mul]; refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg w (Real.exp_pos _).le)); rw [mul_assoc, ←Real.exp_add]; apply le_mul_of_one_le_right (by norm_num); apply Real.one_le_exp; linarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr h) s]
 cases j with
 | inl i=>
    by_cases f:r < Font.dial x (Sum.inl i); · exact he _ f.le
    have hy: i.1∉ flags v U:= by intro W; apply t; apply halo_spec.mpr; exact ⟨i.1,W,(separation_comm ..).trans_le (le_of_not_gt f)⟩
    let y:=i.1; let p:Face (Per (More N)):= i; have hh: group.chord (faceValue U p) ≤ v:=by
       by_contra! t; exact hy ((flags_spec ..).mpr ⟨i,Work.E01.base_touched _,t⟩)
    apply (group.curvature_norm _).trans; let T:=shiftH x y; have ht:stop x T=y:=stopH ..; rw [Nacre.boot, travel_append,travel_append,stop_append]; simp_rw [show stop x (shiftH x i.1)=i.1 from ht,square_stop]; rw [show travel U i.1 _= _ from (show travel U y (reverse T)=(travel U x T)⁻¹ from (by nth_rw 1 [←ht]; rw [travel_reverse]))]; rw [group.chord_conj]
    exact hh.trans (le_trans (le_add_of_nonneg_right (by positivity)) (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))))
 | inr i=> exact he _ e
variable {m:ℕ}
private def Hawk (S:Finset (Seat N)):Finset (Single N):= univ.filter (fun i=> place_x i ∈ S)
open Tenant
lemma whak_budget (S:Finset (Seat N)):(Hawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Hawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Hawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
open Fixed.Extensive
private lemma bolt_saw (U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(i:Signed) :
    absEntries (cavil T (Yg (Nacre.incX i) (A0 U))) ≤ storm U v e r d C m:=by
 let A:= Yg (Nacre.incX i) (A0 U); let B:= (Lattice.halo d (flags v A)); let H:= Hawk B; let D:=45*((2:ℝ)^m*C); let E:=45*(e^m*C); let y:=quake r d (flakes v U.1); let f(j:Single N) := ∑ k:Single N, ‖cavil T A j k‖
 have hp : 0≤ v+2*Real.exp (-(a*d)):=by positivity
 have ht:0≤E:=by unfold E; have he:=hp.trans q; positivity
 have he:(∑ j,f j) ≤ ∑ j:Single N,(E+if j∈ H then D else 0):=by
    apply sum_le_sum; intro j _; split
    · exact (Fixed.Extensive.cavilRow T p (A0 U) (railT _ _ s) s (by positivity) i j).trans (le_add_of_nonneg_left ht)
    rename_i V; rw [add_zero]; apply le_trans (cavil_row_reduced T p (A0 U) s hp i j (leafRow A (place_x j) (fun k=>V (mem_filter.mpr ⟨mem_univ _,k⟩)) l w s)); unfold E; gcongr
 have hv:B=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold B A; rw [Ywin i]
 apply he.trans; rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero]; simp_rw [card_univ,nsmul_eq_mul,add_zero]; rw [filter_mem_eq_inter,univ_inter]; unfold storm; gcongr
 have hk:= grease_f g U ℓ d i; rw [←hv] at hk
 have hz:= (whak_budget B).trans (Nat.mul_le_mul_right 180 hk); have he:(H.card:ℝ)≤ y:= by unfold H y quake flakes; exact (Nat.cast_le.mpr hz).trans (Eq.le (by push_cast; ring))
 exact he
private lemma pays_foil_sum (F:Signed→ FC (Single N)) (C:ℝ) {v:ℝ}(H:∀ s,Pays v (F s) C): Pays v ((Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,F s) C:=by
 let Q:=Fintype.card Signed; have ht:= (Pays.sumT univ F (fun _=> C) (fun x _=>H x)).linear ((Q:ℝ)⁻¹:ℝ)
 have he : 0<(Q:ℝ):=by unfold Q; exact_mod_cast Fintype.card_pos
 rw [Complex.norm_real,Real.norm_of_nonneg (by positivity),sum_const,card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ he.ne'] at ht -- syntactic Q issue
 exact ht
private lemma tender_dT {h:ℝ}(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) (P:Op (Single N))(Hp:IsStarProjection P) : Pays h (dg (Kennel.capT P (colorX T (A0 U)))) (storm U v e r d C m*h^2):=by
  let Q:=1-P; let K : Op (Single N) →ₗ[ℝ] FC (Single N):=
    { toFun F:=dg (Q*F*P)
      map_add' i j:=by rw [mul_add,add_mul,dg_add]
      map_smul' c F:=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,dg_scale]; rfl }
  let D(s):= Nacre.foil s (cavil T) (A0 U)
  change Pays h (K (_ • ∑ s:Signed,D s)) _
  rw [map_smul,map_sum]; apply pays_foil_sum; intro i; let L:= cavil T (Yg (Nacre.incX i⁻¹) (A0 U))
  change Pays h (dg (Q* Nacre.foil i (cavil T) (A0 U)*P)) _ ; rw [Nacre.foil,Nacre.zone_c]
  exact (Pays.jazzG hH _ _ L Q P (Hp.one_sub.norm_le _) (Hp.norm_le _)).weigh (mul_le_mul_of_nonneg_right (bolt_saw U g ℓ s w l T p c e q i⁻¹) (sq_nonneg _)) hH
private lemma dgActC {h β γ D:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D β γ a C R)(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))) : Pays h (dg (actF j R A0 U)) ((storm U v e r d C 1+storm U v e r d C 2)*h^2):=by
 unfold actF Aim.den; rw [Pi.add_apply]; obtain ⟨A,B⟩:= L.field.1
 rw [show ∀ (x y z:Op (Single N)),Kennel.capT x (y+z)=Kennel.capT x y+Kennel.capT x z from fun _ _ _=>by unfold Kennel.capT; rw [mul_add,add_mul],dg_add,add_mul]
 exact (tender_dT hH U g ℓ s w l _ A c e q _ p).add (tender_dT hH U g ℓ s w l _ B c e q _ p)
open CF.Py.Rate
private lemma pang {d r:ℕ}{C h:ℝ}(c:0≤C) (p:0≤h)(e:ℝ)(U:Orbit N)(v:ℝ) : (storm U v e r d C 1+storm U v e r d C 2)*h^2 ≤ (180*45*C*h^2*(e+e^2))*(((N.val:ℕ):ℝ)^4) + (quake r d 1*(45*6*C)*h^2)*flakes v U.1 := by
 apply le_of_eq; unfold storm quake; rw [Pic.units_t (N:=N)]; ring
private lemma bedtime (a X:ℝ)(s:0<a)(l:0<X) : ∃ d:ℕ,2*Real.exp (-(a*d)) ≤ X:=by
 apply Filter.Eventually.exists (f:=atTop); have ht:Tendsto (fun i:ℕ=> 2*Real.exp (-(a*i))) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop s))).const_mul 2))
 exact ht.eventually (ge_mem_nhds l)
private def grime(r d:ℕ)(η:ℝ):=4*η*(((r+4)*2+1:ℕ)^4:ℕ)*((d+d+1:ℕ)^4:ℕ)
private lemma pigment_d (p:Pec.Pride N)(v':Pec.Lac p a C)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v≤ u) (x:0≤v)(y:0≤a)(w:0≤ C)(l:d ≤(More N).val)(e:ℝ)(q:v+2*Real.exp (-(a*d)) ≤ e) : ‖Pec.pigment p (A0 U)‖ ≤ (N.val:ℝ)^4*(C*e^2)+grime r d (flakes v U.1)*(C*4):=by
 apply sealV; intro i; let V:=Yg (Nacre.incX i) (A0 U); let B:= Lattice.halo d (RG.flags v V); let S:= (univ:Finset (Site N)).filter fun i=> node i∈ B; have he:S.card ≤ B.card:=by rw [←card_image_of_injective S Tenant.needle]; exact card_le_card (image_subset_iff.mpr fun _ x=> (mem_filter.mp x).2)
 have hp:(B.card:ℝ)≤ grime r d (flakes v U.1):=by have ht:= grease_f g U ℓ d i; unfold B V; rw [Ywin]; exact (Nat.cast_le.mpr ht).trans_eq (by unfold grime flakes; push_cast; ring)
 have hz (e:ℝ)(x:Site N)(z:0 ≤ e)(w:RayPrice V (node x) e a) : ‖Pec.tag (node x) (p x) V‖ ≤ C*e^2:=by
    let n:= node x
    have ht(i j:Pec.Ok N): ‖inner ℝ (silt n i V) (silt n j V)‖≤ e^2* nick a (contour n i j):=by
       apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (w i) (w j) (norm_nonneg _) (mul_nonneg z (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos (node x) i j])) (by positivity)
    apply (norm_sum_le ..).trans; apply le_trans (b:= Pec.cents n (p x) a *e^2) _ (mul_le_mul_of_nonneg_right (v'.pay x) (sq_nonneg _)); unfold Pec.cents; simp_rw [sum_mul]; refine sum_le_sum fun i _=> ?_; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_ ; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (ht i j) (norm_nonneg _)).trans_eq (by ring)
 rw [Pec.complX]; have hq(j): ‖cSignX (detX i) j‖= ‖j‖:=by unfold cSignX; split; simp; rfl
 rw [hq]; change ‖Pec.zinger p V‖≤_; apply (norm_sum_le ..).trans
 have hh:=show 0≤ v+2*Real.exp (-(a*d)) from by positivity
 let f(x:Site N):=C*e^2+if x∈S then C*4 else 0
 refine (sum_le_sum (g:=f) ?_).trans ?_
 · intro j g; change ‖Pec.tag (node j) (p j) V‖≤ f j; unfold f; split
   next h=>
      refine (hz 2 _ zero_le_two (fun s=> (railT (A0 U) a y|>.fee i (node j) s))).trans (by have ht:=mul_nonneg w (sq_nonneg e); linarith)
   next h=>
      obtain ht:= leafRow V (node j) (fun g=>h (mem_filter.mpr ⟨mem_univ _,g⟩)) l x y
      rw [add_zero]; exact (hz _ j hh ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh q _) w)
 unfold f; rw [sum_add_distrib,sum_const, ← sum_filter]; simp only [filter_mem_eq_inter, univ_inter,sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow]; exact add_le_add_right (mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr he).trans hp) (by positivity)) _

private lemma full_t {D u₁ u₂ h:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D u₁ u₂ a C R)(hH:0≤h)(hw:h≤D)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))) : Pays h (mile j R A0 U) (Real.exp ((N.val:ℝ)^4*(C*e^2)+grime r d (flakes v U.1)*(C*4)+((u₁+u₁+u₂)*(More N).val^4+ (storm U v e r d C 1+storm U v e r d C 2)*h^2))) :=by
 have h₀:= dgActC R L hH U g ℓ s w l c e q p; have he:= Pays.boardH N R U u₁ u₂ C a D L _ p hH hw
 let Q:=Pec.pigment R.J.I (A0 U); let E:=(N.val:ℝ)^4*(C*e^2)+grime r d (flakes v U.1)*(C*4); have hf:‖-Q‖ ≤ E:= by rw [norm_neg]; exact pigment_d _ L.field.2 U g ℓ w s c l e q -- unused param
 apply (((he.mul h₀.expo).linear (Complex.exp (-Q))).weigh ?_ hH)
 rw [Real.exp_add, Real.exp_add ((u₁+u₁+u₂)*_)]
 exact mul_le_mul_of_nonneg_right ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp_of_le hf)) (by positivity)

open Pressure
-- ALL Roof. Receive small u1 u2 etc separately. enough eventually
lemma lantern {h a C u t:ℝ}{r:ℕ}(p:0≤h)(c:0≤C)(uP:0<u)(s:0<a)(ε:ℝ)(v:0<ε): ∃ κ : ℝ,0≤κ ∧ ∀ᶠ x:ℝ in atTop,∃ n:ℕ,∀ {N:Side}{R:GramM N}{A0:Loom N}(p₁:Roof N u t r A0) (D u₁ u₂:ℝ)(j:ℕ)(l:Ledger D u₁ u₂ a C R), h≤ D → n≤ N.val → u₁ ≤ ε/6 → u₂ ≤ ε/6 → ∀ z:Orbit N, IsStarProjection (spar j R.J.M (A0 z)) → Pays h (mile j R A0 z) (Real.exp (ε*sites N + κ*flakes (temp x) z.1)):=by
 let f(y:ℝ):=C*y^2+180*45*C*h^2*(y+y^2); have he:Continuous f:=by unfold f; fun_prop
 have hh:f 0 < ε/2:= by simpa [f] using half_pos v
 have hf: ∀ᶠ i:ℝ in nhdsWithin 0 (Set.Ioi 0),f i< ε/2 := eventually_nhdsWithin_of_eventually_nhds (he.continuousAt.tendsto.eventually (gt_mem_nhds hh)); obtain ⟨e,he',t'⟩:= (hf.and self_mem_nhdsWithin).exists; change 0 < e at t'
 obtain ⟨d,l⟩:=bedtime a (e/2) s (half_pos t')
 let k:=quake r d 1*(45*6*C)*h^2; let P:= k+grime r d 1*(C*4); refine ⟨P,by unfold P k quake grime; positivity,?_⟩; have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (ge_mem_nhds (half_pos t')),ht.eventually (ge_mem_nhds uP)] with x hx v0 w; let y:= temp x; refine ⟨d,fun {N R A0} a' D u₁ u₂ j H hv hd h1 h2 Z X =>?_⟩
 have h0:y≥0:= (Work.E09.temp_pos hx).le
 have hl := full_t (u:=u) R H p hv Z a' w s.le h0 (hd.trans (Nat.le_mul_of_pos_right _ two_pos)) c e (show y+2*Real.exp (-(a*(d:ℝ)))≤e from (by change y≤e/2 at v0; linarith only [v0,l])) X
 refine hl.weigh (Real.exp_monotone ?_) p
 apply (add_le_add_right (add_le_add_right (pang (d:=d) (r:=r) c p e Z y) _) _).trans
 let V:= sites N; let W:=((N.val:ℝ)^4)
 have H' : W ≤ V:= pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_mul_of_pos_right N.val (by decide : (0:ℕ)<2))) _
 have hp:0≤V:=zero_le_one.trans (sites_pos _); have ht':0≤W:=by unfold W; positivity
 let F:= flakes y Z.1
 change W*_+grime r d F*(C*4)+((u₁+u₁+u₂)*V+(_*W+k*F)) ≤ ε*V + P*F
 have ht:F*grime r d 1=grime r d F:=by unfold grime; ring
 rw [← ht]; unfold f at he'; unfold P
 change W*_+F*grime r d 1*(C*4)+((u₁+u₁+u₂)*V+(_*W+k*F)) ≤ ε*V +(k+grime r d 1*(C*4))*F
 linarith only [mul_le_mul_of_nonneg_right h1 hp,mul_le_mul_of_nonneg_right h2 hp,mul_le_mul_of_nonneg_right he'.le ht',mul_le_mul_of_nonneg_left H' v.le]

/-! # Need even higher tier on dg only. No IncX enlarge. -/
private lemma tiltX {D u₁ u₂ h:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D u₁ u₂ a C R)(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))) : Pays h (Complex.exp (-Pec.pigment R.J.I (A0 U)) • exp (dg (actF j R A0 U))) (Real.exp ((N.val:ℝ)^4*(C*e^2)+grime r d (flakes v U.1)*(C*4)+(storm U v e r d C 1+storm U v e r d C 2)*h^2)) :=by
 have h₀:= dgActC R L hH U g ℓ s w l c e q p
 let Q:=Pec.pigment R.J.I (A0 U); let E:=(N.val:ℝ)^4*(C*e^2)+grime r d (flakes v U.1)*(C*4); have hf:‖-Q‖ ≤ E:= by rw [norm_neg]; exact pigment_d _ L.field.2 U g ℓ w s c l e q
 apply ((h₀.expo.linear (Complex.exp (-Q))).weigh ?_ hH)
 rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp_of_le hf)) (Real.exp_pos _).le
lemma lanternX {h a C u t:ℝ}{r:ℕ}(p:0≤h)(c:0≤C)(uP:0<u)(s:0<a)(ε:ℝ)(v:0<ε): ∃ κ : ℝ,0≤κ ∧ ∀ᶠ x:ℝ in atTop,∃ n:ℕ,∀ {N:Side}{R:GramM N}{A0:Loom N}(p₁:Roof N u t r A0) (D u₁ u₂:ℝ)(j:ℕ)(l:Ledger D u₁ u₂ a C R), n≤ N.val →  ∀ z:Orbit N, IsStarProjection (spar j R.J.M (A0 z)) → Pays h (Complex.exp (-Pec.pigment R.J.I (A0 z)) • exp (dg (actF j R A0 z))) (Real.exp (ε*sites N + κ*flakes (temp x) z.1)):=by
 let f(y:ℝ):=C*y^2+180*45*C*h^2*(y+y^2); have he:Continuous f:=by unfold f; fun_prop
 have hh:f 0 < ε/2:= by simpa [f] using half_pos v
 have hf: ∀ᶠ i:ℝ in nhdsWithin 0 (Set.Ioi 0),f i< ε/2 := eventually_nhdsWithin_of_eventually_nhds (he.continuousAt.tendsto.eventually (gt_mem_nhds hh)); obtain ⟨e,he',t'⟩:= (hf.and self_mem_nhdsWithin).exists; change 0 < e at t'
 obtain ⟨d,l⟩:=bedtime a (e/2) s (half_pos t')
 let k:=quake r d 1*(45*6*C)*h^2; let P:= k+grime r d 1*(C*4); refine ⟨P,by unfold P k quake grime; positivity,?_⟩; have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (ge_mem_nhds (half_pos t')),ht.eventually (ge_mem_nhds uP)] with x hx v0 w; let y:= temp x; refine ⟨d,fun {N R A0} a' D u₁ u₂ j H hd Z X =>?_⟩
 have h0:y≥0:= (Work.E09.temp_pos hx).le
 have hl := tiltX (u:=u) R H p Z a' w s.le h0 (hd.trans (Nat.le_mul_of_pos_right _ two_pos)) c e (show y+2*Real.exp (-(a*(d:ℝ)))≤e from (by change y≤e/2 at v0; linarith only [v0,l])) X
 refine hl.weigh (Real.exp_monotone ?_) p
 apply (add_le_add_right (pang (d:=d) (r:=r) c p e Z y) _).trans
 let V:= sites N; let W:=((N.val:ℝ)^4)
 have H' : W ≤ V:= pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_mul_of_pos_right N.val (by decide : (0:ℕ)<2))) _
 have hp:0≤V:=zero_le_one.trans (sites_pos _); have ht':0≤W:=by unfold W; positivity
 let F:= flakes y Z.1
 change W*_+grime r d F*(C*4)+(_*W+k*F) ≤ ε*V + P*F
 have ht:F*grime r d 1=grime r d F:=by unfold grime; ring
 rw [← ht]; unfold f at he'; unfold P
 change W*_+F*grime r d 1*(C*4)+(_*W+k*F) ≤ ε*V +(k+grime r d 1*(C*4))*F
 linarith only [mul_le_mul_of_nonneg_right he'.le ht',mul_nonneg v.le ht',mul_le_mul_of_nonneg_left H' v.le]
end YM.CF.Pannier.Damask
#print axioms YM.CF.Pannier.Damask.lantern
