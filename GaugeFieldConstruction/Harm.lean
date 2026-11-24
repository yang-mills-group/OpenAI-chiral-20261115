/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Next.FREE_KERNELS.Sprout
import YM.CF.Peaks.Lintel
set_option autoImplicit false
set_option maxHeartbeats 32000
set_option linter.unusedVariables false
noncomputable section
namespace YM.Next.Free
open Filter Function Lattice Laurent Bloch Metric Finset Exterior Precision
open scoped Topology BigOperators Classical ComplexConjugate
namespace HarmP
private def priceB (x:ℤ):ℝ:= (1+(x.natAbs:ℝ))⁻¹
private lemma costD (n:ℕ): ∑ i∈ range (n+1),priceB ↑i ≤ 1+Real.log (n+1:ℝ):=by
 induction n with
 | zero=>simp [priceB]
 | succ n ih =>
    have ht:(n:ℝ)<n+1:=lt_add_one _; have hx:0< (n+1:ℝ):=(by positivity); have hv:0<(n+1+1:ℝ):=by positivity
    rw [sum_range_succ]; apply (add_le_add_left ih _).trans; unfold priceB; norm_cast -- tune
    push_cast; have he:= Real.log_le_sub_one_of_pos (div_pos hx hv); rw [Real.log_div (ne_of_gt hx) (ne_of_gt hv)] at he;
    have hp: ((n:ℝ)+1)/(n+1+1)-1= -(1+(n+1:ℝ))⁻¹:=by field_simp; ring
    linarith
abbrev Rocket (L:Side):ℝ:=4*(1+Real.log L.val)
abbrev SpanL (L:Side):ℝ:=(Rocket L)^4
lemma rocket_one (L:Side):1 ≤ Rocket L:= by unfold Rocket; have ht:0 ≤ Real.log L.val:=Real.log_nonneg (by exact_mod_cast L.property); linarith
lemma span_one (L:Side):1 ≤ SpanL L:=one_le_pow₀ (rocket_one _)
lemma harm (L:Side): ∑ i:Site L, decay 1 i ≤ SpanL L:=by
 have he(x:Site L):decay 1 x=∏ i:Axis,priceB (lift x i):=by simp [decay,mix,up,priceB]
 have hf : Function.Injective (fun i : ZMod L.val => i.valMinAbs) := fun i j h => by simpa using congr_arg (fun z : ℤ => (z : ZMod L.val)) h
 have hp(i:ℤ):0 ≤ priceB i:=by unfold priceB; positivity
 have hb:(∑ i:ZMod L.val,priceB i.valMinAbs) ≤ Rocket L:=by
    let X:Finset ℕ:= range (L.val+1); let A:ℕ→ℤ:= ((↑) :ℕ→ℤ); let B(n:ℕ):ℤ:=-↑n
    have hz: univ.image (fun i:ZMod L.val=>ZMod.valMinAbs i) ⊆ (X.image A)∪ (X.image B):=by
       rintro x h; obtain ⟨i,g,rfl⟩:=mem_image.mp h; have hg:= i.natAbs_valMinAbs_le -- tune
       have ht: i.valMinAbs.natAbs ≤ L.val:= by omega
       apply mem_union.mpr; let k:=i.valMinAbs.natAbs; have hh:k∈X:=mem_range.mpr (Nat.lt_add_one_iff.mpr ht); by_cases he:0 ≤ i.valMinAbs; exact Or.inl (mem_image.mpr ⟨k,hh, Int.natAbs_of_nonneg he⟩); exact Or.inr (mem_image.mpr ⟨k,hh,(by unfold k B; omega)⟩)
    rw [← sum_image hf.injOn]; refine (sum_le_sum_of_subset_of_nonneg hz (fun i _ _=> hp i)).trans (( ((le_add_of_nonneg_right (sum_nonneg (s:=X.image A∩X.image B) fun i _=> hp i)).trans_eq sum_union_inter)).trans ?_)
    let H:=1+Real.log (L.val+1:ℝ); have hX:∑ i∈X,priceB (A i) ≤ H:= costD _; rw [sum_image (show Function.Injective A from fun i j h=> Int.natCast_inj.mp h).injOn, sum_image (show Function.Injective B from fun i j h=> Int.natCast_inj.mp (neg_inj.mp h)).injOn]; simp_rw [show ∀ i,priceB (B i)=priceB (A i) from fun i=> by simp [B,A,priceB]]; apply (add_le_add hX hX).trans
    have hx: 1≤(L.val:ℝ):=by exact_mod_cast L.property
    have hp:=zero_lt_one.trans_le hx
    have he:Real.log (L.val+1:ℝ) ≤ Real.log (2*(L.val:ℝ)):=Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hp.ne'] at he; unfold H Rocket; linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 from by norm_num),Real.log_nonneg hx]
 simp_rw [he]; unfold lift Site Four; rw [←Fintype.prod_sum (κ:= fun _ : Axis => Per L) (fun _ x => priceB (ZMod.valMinAbs x))]; calc
 _ ≤ ∏ _ : Axis, Rocket L := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hp _) (fun _ _ => hb)
 _= _:=by simp [SpanL,Axis]
variable {j t:ℕ}{α β:Type*}{f:Thread j t α β}
lemma propels (h:Secured f)(e:ℕ)(u:List Axis)(v:u.length+1≤j) {ι:Type*}(F:ι→ Flight j t)(r:∀ i, Site (F i).L): Pay (fun i => (((F i).L.val:ℝ)^(e+u.length))⁻¹*SpanL (F i).L) fun i=> Next.Free.spread f e u (F i) (r i):=by
 refine ⟨fun i=>mul_nonneg (by positivity) (zero_le_one.trans (span_one _)),fun a b=>?_⟩; simp only [Next.Free.spread,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
 let L(i:ι):=(F i).L; let y(i):= (((L i).val:ℝ)^(e+u.length))⁻¹; let s (i):= (univ:Finset (Site (L i)))
 apply Moderate.sum_family s (fun i l => y i*decay 1 l) ⟨1,one_pos,fun i => (by
    rw [← Finset.mul_sum,one_mul]; exact mul_le_mul_of_nonneg_left (harm (L i)) (by unfold y; positivity))⟩
 let I := Σ i, {l // l∈s i}; let m (i : I) := F i.1; let q (i : I) := i.2.val
 have he := differential_bound m q e u; have hp := residue_cost m q (fun i => r i.1); have hc := (h.pay.tap a b).index (fun i => ⟨m i,q i⟩)
 apply (hp.mul (he.mul hc)).raise_price; intro i; dsimp only; rw [one_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
 apply (mul_le_mul_of_nonneg_left (decay_anti _ (show 1+u.length≤j by omega)) (pow_nonneg (grade_pos _).le _)).trans (absorbs ..)
lemma scopeB [Fintype α][Fintype β] (h: Secured f)(e:ℕ){u:List Axis}(p:u.length+1≤j):∃ σ C:ℝ,0<σ∧0<C ∧∀ P:Flight j t,(meshBook f e u P).strip σ (C*(SpanL P.L/(P.L.val:ℝ)^(e+u.length))):= by
 obtain ⟨σ,C,hσ,hC,H⟩:= matrix_cover (propels h e u p (fun i: Σ P: Flight j t, Site P.L=>i.1) (fun i=>i.2)) zone_pos (fun i _ hp x hx => h.layout e u _ _ hp x hx)
 refine ⟨σ,C,hσ,hC,fun P ⟨r,a⟩ b=>?_⟩; rw [div_eq_mul_inv,mul_comm (SpanL P.L)]; exact H (⟨P,r⟩:Σ P:Flight j t, Site P.L) a b
lemma scope_S [Fintype α] [Fintype β](h:Secured f)(e:ℕ){u:List Axis}(p:u.length+1≤j)(P: Flight j t) : (meshBook f e u P).safe:=by obtain ⟨_,_,t,h,H⟩:=scopeB h e p; exact Row.rights _ _ (H _) t.le
lemma scope_R (h:Secured f)(e:ℕ){u:List Axis}(p:u.length+1≤j)(P:Flight j t) (r:Site P.L){q:Momentum}(H:q∈baseCube)(a:α)(b:β): (meshBook f e u P).read q (r,a) b=Next.Free.spread f e u P r q a b:=by
 let I := Σ P : Flight j t, Site P.L; have hh := record_eq (propels h e u p (fun i : I => i.1) (fun i => i.2)) zone_pos (⟨P,r⟩:I) (fun i _ hp x hx => h.layout e u _ _ hp x hx) (fun i p hp => h.palette e u _ _ hp) H
 exact congr_fun (congr_fun hh _) _
lemma traverses [Fintype α] [Fintype β](h:Secured f)(e:ℕ){u:List Axis}(v:u.length+1≤j)(P:Flight j t): advanceC P.L (meshBook f e [] P) u = meshBook f e u P:= by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have hh : u.length+1≤j := by rw [List.length_cons] at v; omega
    rw [advanceC,ih hh]
    have h1 := scope_S h e v P; have h₂ := scope_S h e hh P
    funext ⟨l,i⟩ m
    let t p := meshBook f e u P (p,i) m
    let k := carryStep a l; let b := l+step a
    have ht := shift_sound (t b) (h₂ _ _) k
    change (fun z => t b (z-k)-t l z)=_
    apply RRead_injective (ht.of_norm.sub (h₂ _ _).of_norm).norm (h1 _ _)
    intro p hx
    rw [market_sub ht (h₂ _ _) p hx.1, market_move]
    change mode p k * (meshBook f e u P).read p (b,i) m-(meshBook f e u P).read p (l,i) m = (meshBook f e (a::u) P).read _ _ _
    rw [scope_R h e hh _ b hx,scope_R h e hh _ l hx,scope_R h e v _ l hx,enters]; rfl
lemma hon_P [Fintype α][Fintype β](h:Secured f)(e:ℕ)(s:ℕ)(v:s+1 ≤ j):∃ σ C:ℝ,0<σ ∧0<C∧∀ (P:Flight j t)(u:List Axis), u.length≤ s → (advanceC P.L (meshBook f e [] P) u).strip σ (C * (SpanL P.L/(P.L.val:ℝ)^(e+u.length))):=by
 let K:Type := {i: List Axis // i.length ≤ s}; letI: Fintype K:=(Secured.limited_lengths s).fintype
 obtain ⟨σ,C,hp,hC,H⟩ := staple (κ:=K) (fun l σ C => ∀ P, (meshBook f e l.val P).strip σ (C*(SpanL P.L/(P.L.val:ℝ)^(e+l.val.length)))) (fun l => scopeB h e (Nat.le_trans (Nat.succ_le_succ l.property) v)) (fun l _ _ _ _ hv hσ hp hC P a b => (hv P a b).mono hσ (mul_le_mul_of_nonneg_right hC (div_nonneg (zero_le_one.trans (span_one _)) (by positivity))))
 exact ⟨σ,C,hp,hC,fun P u hu => by rw [traverses h e (by omega)]; exact H ⟨u,hu⟩ _⟩
end HarmP
end YM.Next.Free
end
