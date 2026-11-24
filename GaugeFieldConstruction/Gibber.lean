import GaugeFieldConstruction.Pillion
/-! # Wisp ecost before tilting signed trees: from Fronds. Adapted from its budgeting here -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Pannier.Damask
namespace VelvetP
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
open RG
-- explicit ramp. outside a dirty halo.
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
open Tenant
open Fixed.Extensive
open CF.Py.Rate
open Pec
abbrev paintE (d:ℕ)(U:Orbit N)(v y C:ℝ):ℝ:=pittance N y C+ quake r d 1*4*C*flakes v U.1
private lemma cents_i (U:Pane N)(T:Pride N)(j:Site N)(h:Lac T a C)(g:RayPrice U (node j) v a)(e:0≤v):‖tag (node j) (T j) U‖≤v^2*C:=by
 have ht(x t: Ok N): ‖inner ℝ (silt (node j) x U) (silt (node j) t U)‖ ≤ v^2* nick a (contour (node j) x t):=by
    apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (g x) (g t) (norm_nonneg _) (mul_nonneg e (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos (node j) x t])) (by positivity)
 apply (norm_sum_le ..).trans; apply (mul_le_mul_of_nonneg_left (h.pay j) (sq_nonneg v)).trans'; simp_rw [Pec.cents,mul_sum]; refine sum_le_sum fun x _=> (norm_sum_le ..).trans (sum_le_sum fun y _=>?_); rw [norm_smul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht x y) (norm_nonneg _)
private lemma aurPenn (X:Pane N)(T:Pride N)(h:Lac T a C)(U:Orbit N)(p:X=A0 U)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0≤C) (e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) :‖pigment T X‖≤paintE (r:=r) d U v e C:=by
 subst X; apply sealV; intro i; let Y:= A0 U; let Z:=Yg (incX i) Y; let K:= (Lattice.halo d (flags v Z)); let V:= univ.filter (fun j:Site N=> node j ∈ K)
 have hv: (V.card:ℝ) ≤ quake r d 1 * flakes v U.1:=by
    rw [← card_image_of_injective V (Tenant.needle)]; have hz: (Lattice.halo d (flags v Z))=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold Z Y; rw [Ywin i];
    have he:= (card_le_card (show V.image node ⊆ K from image_subset_iff.mpr fun j v=>(mem_filter.mp v).2)).trans (show K.card ≤ (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4) from (by unfold K; rw [hz]; exact grease_f g U ℓ d i)); let n:= (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4); apply le_trans (Nat.cast_le.mpr he); change (n:ℝ) ≤ quake _ _ 1 * flakes v U.1;
    rw [show quake r d 1 * flakes v U.1=(n:ℝ)*180 from (by unfold quake n flakes; push_cast; ring)]; exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by norm_num) -- need normalizing cast
 let E0:= 2^2*C
 have hE: ∀ t:Site N, ‖tag (node t) (T t) Z‖ ≤ e^2*C+ (if t∈ V then E0 else 0):=by
    intro t; split; next _=> exact (cents_i Z T t h (fun u=>(railT (A0 U) _ s).fee i _ u) (by norm_num : (0:ℝ)≤2)).trans (le_add_of_nonneg_left (by positivity : 0≤ e^2 *C)) -- scope rfl?
    next p=>
      have hp:v+2*Real.exp (-(a*d))≥0:=by positivity
      rw [add_zero]; exact (cents_i Z T t h (leafRow Z (node t) (fun v=>p (mem_filter.mpr ⟨mem_univ _,v⟩)) l w s) hp).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp q _) c)
 let F:=zinger T Z; have he:‖F‖ ≤ paintE (r:=r) d U v e C:=by
    apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun t=> e^2*C+(if t∈ V then E0 else 0)) fun j _=>hE j).trans ?_); rw [sum_add_distrib,sum_ite,sum_const_zero,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul, add_zero, filter_mem_eq_inter,univ_inter,card_univ,site_card,Nat.cast_pow]
    exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hv (show 0≤ E0 by unfold E0; positivity)) _) (Eq.le (by unfold paintE pittance E0; ring))
 rw [complX]; unfold cSignX; split <;> (try rw [norm_star]) <;> exact he
open YM.Gleam clocks CF.Sour.SliceRoof
open YM.Pressure Work.E09
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort
/- Native-price tag per pale estimate, consume reserve now.
   We give a slightly different budget from (53): grey plus POSSIBLE FLAG reserve in (51), reducing later credits. -/
abbrev lad_z (V:Pane N)(q:Clip)(x β:ℝ):ℝ:=saveZ x* (Fintype.card (Site (More N)):ℝ) + boldTicket q β x* (misdemean (badgeDust x) V).card
lemma quadBill (a:ℝ)(r:ℕ): RunRate 0 0 (fun x=>quake r (clocks.height x) a):=by
 unfold quake; push_cast
 convert ((((heightT.cmul 2).add (RunRate.const 1)|>.pow 4).cmul (4*a*((r+4:ℝ)*2+1)^4)).muc 180) using 1
 · ring
 · ring
 ext x; ring
lemma closeF (a:ℝ)(p:0<a) : RunRate (-1) 0 (fun x=>Real.exp (-(a* (clocks.height x:ℝ)))):=by
 have he:= trailFees (G:=SU.group) p; unfold trail at he; simpa only [neg_mul] using he
lemma badgePower :RunRate (-(1/4)) 0 badgeDust:= ((RunRate.coins (6*gratuity) 0 0).mul RunRate.temps).relax (by norm_num [gratuity])
lemma tax_p (t:ℝ)(c:0 ≤ C)(q:Clip)(r:ℕ)(p:0<a)(w:0<u)(x:ℝ)(z:0<x): ∀ᶠ y:ℝ in atTop, ∀ β:ℝ,y/2≤β → ∀ {N:Side}{A0:Loom N},Skye.Roof N u t r A0→ clocks.height y ≤ (More N).val → ∀ (T:Pride N)(V:Orbit N), Pec.Lac T a C → ‖Pec.pigment T (A0 V)‖ ≤ x * lad_z V.1 q y β :=by
 let F:=fun y=> badgeDust y+2*Real.exp (-(a* (clocks.height y:ℝ)))
 have hv:RunRate (-(1/4)) 0 F:=badgePower.add (((closeF a p).cmul 2).relax (by norm_num))
 have hg:= q.tail_pos; let A:= x*q.linear/2; have hA:0<A:=by unfold A; positivity
 filter_upwards [eventually_gt_atTop (0:ℝ),badge_ok, badgePower.tends (by norm_num)|>.eventually (ge_mem_nhds w),logPrice _ _ ((hv.pow 2).muc C) (c:=-gratuity/2) (w:=0) (d:=0) (by norm_num [gratuity]) z, logPrice _ _ (((quadBill 1 r).muc 4).muc C) (c:=6*gratuity) (w:=0) (d:=2) (by norm_num [gratuity]) hA] with y uY e b l T β k N A0 v i D V C'
 have hp: (N.val:ℝ)^4 ≤ Fintype.card (Site (More N)):=by rw [site_card,Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ two_pos)) _
 apply (aurPenn (t:=t) (A0 V) D C' V rfl v b p.le ((temp_pos uY).le.trans e) i c (F y) le_rfl).trans
 let g:=pittance N (F y) C; let f:=flakes (badgeDust y) V.1; have hg:g≤ x*(saveZ y* (Fintype.card (Site (More N)):ℝ)):= (mul_le_mul l hp (by positivity) (mul_nonneg z.le (BProof.coin_pos ..).le)).trans_eq (mul_assoc ..) -- assoc
 have ht: quake r (clocks.height y) 1*4*C ≤ x*boldTicket q β y:=T.trans (by have he:= boldTrade q _ uY k; unfold A; linarith only [mul_le_mul_of_nonneg_left he z.le])
 have hf:0≤ f:=Nat.cast_nonneg _; rw [lad_z,mul_add]; apply add_le_add hg ((mul_le_mul_of_nonneg_right ht hf).trans_eq ?_); unfold f; rw [mul_assoc]; rfl -- casting? tune

lemma lipWorth (R:Side)(c:0<a)(b d:ℝ) : RunRate (-(1/5)) 0 (fun x=>lipCharge a b d (suitCost R x) (clocks.height x)):=by
 unfold lipCharge
 let t:= ((((heightT.cmul (4:ℝ)).mul (tile_bill R)).cmul BPress.Spin.sphereRate).divc d)
 refine ((RunRate.add (RunRate.relax t (by norm_num [gratuity])) (((closeF a c).cmul 2).relax (by norm_num))).cmul b)
lemma wall_side (U:Side)(p:Odd U.val){r:ℕ}(v:r≤ U.val/2): (largerBill U.val r:ℝ) ≤ 8*(r:ℝ)*(U.val:ℝ)^3:= wall_cheap p v
lemma fringePrice (q:Clip)(L:Side)(x:ℝ)(z:0<x)(b:ℝ)(p:0≤b): ∀ᶠ y in atTop,∀ β:ℝ,y/2≤β→∀ (N:Side)(U:Pane N)(s:Signed){c:Side}(r:Ratio c (More N)),Odd r.count.val→ clocks.Marked y r.count L → b*(cliffCourt U s r (badgeDust y) (clocks.height y)).card ≤ x * lad_z U q y β:=by
 let V(y:ℝ):=2*L.val*tileN y; have he:RunRate gratuity 0 V:=(RunRate.coins ..).cmul _
 let k:=x*q.linear/2; have h₁ : 0 < q.linear:=q.tail_pos; have hk:0<k:=by unfold k; positivity
 filter_upwards [eventually_gt_atTop (0:ℝ),wall_matures L, logPrice _ _ ((hallT.cmul 8).cmul b) (c:= (-gratuity/2)+gratuity) (w:=0) (d:=0) (by norm_num [gratuity]) z,logPrice _ _ ((he.pow 4).cmul (b*21^4)) (c:=6*gratuity) (w:=0) (d:=2) (by norm_num [gratuity]) hk] with y w W l u β hy N U s c R pR m
 have ht:= (outline_bound (r:=R) (broken R (badgeDust y) (pull s 0 U)) pR (W R.count m)); let P:=(Fintype.card (Site c):ℝ); let d:= hallBill (clocks.height y); let M:=(R.count.val:ℝ)
 let A:= (misdemean (badgeDust y) (pull s 0 U)).card; have hx:(A:ℝ)=(misdemean (badgeDust y) U).card:=by simpa only [one_mul] using whirlwind s U 1 (badgeDust y)
 let F:= 8*(d:ℝ)*M^3; have hg: (↑(cliffCourt U s R (badgeDust y) (clocks.height y)).card:ℝ) ≤ P*F+((A:ℝ)*21^4)*M^4:=by
    apply (Nat.cast_le.mpr ht).trans; push_cast; apply add_le_add (mul_le_mul_of_nonneg_left (wall_side _ pR (W _ m)) (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_right _ (show 0 ≤ M^4 by unfold M; positivity)); exact_mod_cast (broken_charge (r:=R) (t:=badgeDust y) (U:=pull s 0 U))
 apply (mul_le_mul_of_nonneg_left hg p).trans
 unfold lad_z; rw [mul_add,mul_add x]; have hd: (Fintype.card (Site (More N)):ℝ)=P*M^4:=by unfold P M; rw [site_card,site_card,R.exact_size]; push_cast; ring
 have h': b*(8*(d:ℝ)) ≤ x*saveZ y*M:=by
    calc _ ≤ x*(saveZ y*tileN y):= by unfold tileN saveZ Rrp; rw [coin_mul,zero_add]; exact l
         _ ≤ _ := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m.1 (BProof.coin_pos ..).le) z.le).trans_eq (mul_assoc ..).symm
 have ht: b*(21:ℝ)^4*M^4 ≤ x*boldTicket q β y:= ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ M from Nat.cast_nonneg _) m.2 4) (by positivity)).trans u).trans (by unfold k; linarith only [mul_le_mul_of_nonneg_left (boldTrade q _ w hy) z.le])
 apply add_le_add
 · unfold F; rw [hd]; nlinarith only [mul_le_mul_of_nonneg_left h' (show 0 ≤ P*M^3 from mul_nonneg (Nat.cast_nonneg _) (by unfold M; positivity))]
 rw [← hx]; nlinarith only [mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (α:=ℝ) A)]

lemma exper (L:Side)(q:Clip) (pa:0<a)(pb:0≤C)(d:ℝ)(h:0<d)(e:ℝ)(u:0<e): ∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2≤β→∀ (N:Side)(A:Orbit N)(s:Signed){c:Side}(V:Ratio c (More N)),Odd V.count.val→ clocks.Marked x V.count L → rentK A s V (badgeDust x) (suitCost L x) a C d (clocks.height x) ≤ e * lad_z A.1 q x β:=by
 filter_upwards [eventually_gt_atTop (0:ℝ),logPrice _ _ ((lipWorth L pa C d).cmul (180:ℝ)) (c:=-gratuity/2) (w:=0) (d:=0) (by norm_num [gratuity]) (half_pos u),fringePrice q L (e/2) (half_pos u) ((C+C)*180) (by positivity)] with x p v w β b N A s c V g i
 have ht: ((N.val:ℕ):ℝ)^4 ≤ Fintype.card (Site (More N)):= by rw [site_card,Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ two_pos)) _
 have hz:= w β b N A.1 s V g i; unfold rentK; rw [Pic.units_t]; let T:= Fintype.card (Site (More N)); let t:=lipCharge a C d (suitCost L x) (clocks.height x)
 have he : (180*(N.val:ℝ)^4)*t ≤ e/2*(saveZ x*T):=by
    apply le_trans (b:=(180*t)*(N.val:ℝ)^4); · exact le_of_eq (by ring)
    rw [←mul_assoc (e/2) (saveZ x)]; exact mul_le_mul v ht (by positivity) (show 0 ≤ (e/2)*saveZ x from mul_nonneg (half_pos u).le (BProof.coin_pos ..).le)
 have hg:=boldTrade q x p b; have ha:0≤boldTicket q β x:= (show 0 ≤ q.linear/2* coin x (6*gratuity) 2 0 from mul_nonneg (half_pos q.tail_pos).le (BProof.coin_pos ..).le).trans hg
 have hp: saveZ x*T≤ lad_z A.1 q x β:= le_add_of_nonneg_right (mul_nonneg ha (Nat.cast_nonneg _))
 change 180* (N.val:ℝ)^4*t + _ ≤ _ -- cast tune
 nlinarith only [hz,he,mul_le_mul_of_nonneg_left hp (half_pos u).le]
end VelvetP
end YM.CF.Pannier.Damask
end
