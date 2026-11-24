/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Harm
/-!
# spin cover prices & motions. No ad-hoc changes on Tor matrices.
-/
set_option autoImplicit false
set_option maxHeartbeats 40000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Laurent Bloch Next.Free HarmP Fir Lat Finset
open Rush Peaks
open scoped Topology Matrix InnerProductSpace BigOperators Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
namespace Thorn
lemma porT (u:Bool)(j:ℕ) {ι:Type*}(L M:ι→Side)(h:∀i,Odd (L i).val)(e:∀i,Odd (M i).val)(r:∀ i, Site (L i))(D:List Axis)(hx:D.length+1≤j): Pay (fun i=> SpanL (L i)*(Real.sqrt (L i).val / ((L i).val:ℝ)^(D.length+2))) fun i=>Fir.paint u j (L i) (M i) (r i) D := by
  refine ⟨fun i=>mul_nonneg (zero_le_one.trans (span_one _)) (by positivity),fun a b=> ?_⟩; simp only [Fir.paint,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let f i:= Real.sqrt (L i).val / ((L i).val:ℝ)^(D.length+2)
  let s (i:ι) : Finset (Site (L i)):=univ
  apply Moderate.sum_family s (fun i l=> f i*Next.Free.decay 1 l) ⟨1,one_pos,fun i=> by rw [← Finset.mul_sum,one_mul,mul_comm (SpanL _)]; exact mul_le_mul_of_nonneg_left (harm _) (by unfold f; positivity)⟩
  let W:= Σ i:ι, {l//l∈s i}; let q(w:W):ι:=w.1; let l(w:W):Site (L w.1):=w.2
  have he := (armPay u j (by omega) (L ∘ q) (M ∘ q) (fun i=>h _) (fun i=>e _) l).tap a b
  have hg:= (peak (L ∘ q) (fun i=>h _) l (fun i=>r _)).mul ((pen (L ∘ q) (fun i=>h _) l D 2).mul he)
  apply hg.raise_price; intro i; dsimp only [q,f,Function.comp_apply] at *; rw [one_mul]
  have hm := ((mul_le_mul_of_nonneg_left (decay_anti (l i) (show 1+D.length≤j by omega)) (pow_nonneg (grade_pos (l i)).le D.length)).trans (absorbs ..))
  calc
    _ = f i.1*((grade (l i))^D.length*Next.Free.decay j (l i)):= by dsimp only [f]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by unfold f; positivity)
variable {L M : Side} {u:Bool}{j:ℕ}
lemma hubWorld (u:Bool)(j:ℕ)(L M:Side)(v:Odd L.val)(e:Odd M.val)(D:List Axis)(h:D.length+1≤j):Reads (tub (coverlet u j L M D)) (coverlet u j L M D):=by
 have he: Pay (fun _:Unit=> SpanL L* (Real.sqrt L.val/(L.val:ℝ)^(D.length+2))) (fun _=> coverlet u j L M D):=by
    unfold coverlet; apply col_quote L; intro i; exact porT u j (fun _=>L) (fun _=>M) (fun _=>v) (fun _=>e) (fun _=>i) D h
 exact Rush.paid he (fun _ p hp x ht=>by dsimp only [coverlet]; congr 1; ext1 i; exact spans _ _ _ _ _ _ hp x ht) ()
abbrev wool (L:Side)(D:List Axis):ℝ:=SpanL L*(Real.sqrt L.val/(L.val:ℝ)^(D.length+2))
lemma wool_pos (L:Side)(D:List Axis):0 ≤ wool L D:=mul_nonneg (zero_le_one.trans (span_one _)) (by positivity)
abbrev Hed (u:Bool)(j:ℕ)(L M: Side)(r:Site L)(a b:SpinIdx)(D:List Axis) (x: Cover) : ℂ:= tub (coverlet u j L M D) x (r,a) (0,b)
lemma WoolTax (u:Bool)(j:ℕ){ι:Type*}(L M:ι → Side)(v:∀ i, Odd (L i).val)(e:∀ i, Odd (M i).val)(r:∀ i,Site (L i))(D:List Axis)(h:D.length+1≤j):∃ σ C:ℝ,0<σ∧0<C∧∀ i a b, Width σ (C*wool (L i) D) (Hed u j (L i) (M i) (r i) a b D):=by
 obtain ⟨⟨σ,C,hσ,hC,H⟩, _⟩:= tub_bill (porT u j L M v e r D h) (fun i p hp x ht=> spans _ _ _ _ _ _ hp x ht)
 refine ⟨σ,C,hσ,hC,fun i a b=> ?_⟩; convert H i a b using 1; ext1 x; simp only [Hed,coverlet,tub,Matrix.of_apply,c_app, if_true]
lemma wool_mode (u:Bool)(j:ℕ)(s:ℕ)(v:s+1 ≤j):∃ σ C:ℝ,0 <σ ∧ 0<C ∧ ∀ (L M:Side), Odd L.val→Odd M.val→∀ (r:Site L)(a b:SpinIdx)(D:List Axis), D.length ≤ s → Width σ (C*wool L D) (Hed u j L M r a b D):=by
 let K:Type := {i: List Axis // i.length ≤ s}; letI: Fintype K:=(Secured.limited_lengths s).fintype
 let Q:= Σ p:Tulip.Male×Tulip.Male, Site p.1.val
 obtain ⟨σ,C,hp,hC,H⟩:=staple (κ:=K) (fun l σ C=>∀ (i:Q) a b,Width σ (C*wool i.1.1.val l.val) (Hed u j _ i.1.2.val i.2 a b l.val)) (fun l=> WoolTax u j (fun i:Q=>i.1.1.val) (fun i=>i.1.2.val) (fun i=>i.1.1.property) (fun i=>i.1.2.property) (fun i=>i.2) l.val (Nat.le_trans (Nat.succ_le_succ l.property) v)) (fun l _ _ _ _ h' g hx hC i a b => (h' i a b).mono g (mul_le_mul_of_nonneg_right hC (wool_pos ..))) -- tune
 exact ⟨σ,C,hp,hC,fun L M e q r a b D v=> H ⟨D,v⟩ (⟨(⟨L,e⟩, ⟨M,q⟩),r⟩:Q) a b⟩
lemma enters_H (u:Bool)(j:ℕ)(L M:Side)(r:Site L)(v:Odd L.val)(a:Axis)(D:List Axis)(p:Momentum): paint u j L M r (a::D) p =mode p (carryStep a r) • paint u j L M (r+step a) D p-paint u j L M r D p := by
 unfold Fir.paint; rw [Finset.smul_sum,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
 let q:=aliasAt p i; have hh:mode p (carryStep a r)* mode q (lift (r+step a))=mode q (lift r)*mode q (step a):=by
    have hx:=congr_arg (mode q) (cover_step v a r); simp only [mode_shift, ← mode_scale,show L.val • q=_ from alias_scale p i,mode_phase,mode_periodic,mul_one] at hx
    rw [mul_comm]; exact hx
 have he : chip (q a)=mode q (step a)-1 := by rw [Exterior.factor]; rfl
 change _ = mode p (carryStep a r) • (mode q _ • _) - mode q _ • _
 simp only [listChip,List.map_cons,List.prod_cons,smul_smul,← sub_smul]; unfold q at *; congr 1; rw [he]; simp only [← mul_assoc]; rw [hh]; ring
lemma shiny(u:Bool)(j:ℕ)(L M:Side)(v:Odd L.val)(e:Odd M.val)(D:List Axis)(h:D.length+1≤j)(p:Momentum)(hp:p∈ baseCube)(r:Site L) (a b:SpinIdx): Laurent.read (Hed u j L M r a b D) p= paint u j L M r D p a b:=by
 rw [show Laurent.read _ _= _ from (hubWorld u j L M v e D h).readK p hp (r,a) (0,b),coverlet,c_app]; simp
private abbrev reK(f:Cover→ℂ)(x:Cover):ℝ:= (f x).re
private lemma resound {f:Cover→ℂ}(p:Summable fun i=>‖f i‖): Summable fun i=> ‖reK f i‖:= Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _) p
lemma reels {f:Cover→ℂ}(v:Summable fun i=>‖f i‖)(p:Momentum)(g:physical p): (2:ℂ) * RRead (reK f) p= Laurent.read f p + star (Laurent.read f (-p)):=by
 have he(k:Momentum)(t:physical k):Summable fun i=> mode k i • f i:=by apply Summable.of_norm; simpa only [norm_smul,mode_real _ _ t,one_mul] using v
 have hx : physical (-p):= by unfold physical; rw [star_neg,g]
 unfold RRead Laurent.read; rw [← tsum_mul_left,tsum_star, ← Summable.tsum_add (he p g) ((he _ hx).star)] -- tune tsum.star
 refine tsum_congr fun i=> ?_; rw [smul_eq_mul,smul_eq_mul,smul_eq_mul]
 have hp:star (mode (-p) i)= mode p i:=by have he:=mode_adjoint (-p) i; rwa [show star (-p)=-p from hx,mode_opposite,←mode_inverse,neg_neg] at he -- tune
 rw [star_mul',hp, ← mul_add]
 have hm:(2:ℂ)*(reK f i:ℝ)=f i + star (f i):=by apply Complex.ext <;> simp [reK,two_mul]
 rw [←hm]; ring
lemma ledger_inj (f g:Cover→ℂ)(p:Summable fun i=>‖f i‖)(u:Summable fun i=>‖g i‖)(h:∀ k∈baseCube,Laurent.read f k=Laurent.read g k): f=g:=by
 have ht(f g:Cover→ℂ)(v:Summable fun i=>‖f i‖)(u:Summable fun i=>‖g i‖)(h:∀ k∈ baseCube,Laurent.read f k=Laurent.read g k):reK f=reK g:=by
    apply RRead_injective (resound v) (resound u); intro k hk; apply mul_left_cancel₀ two_ne_zero; rw [reels v k hk.1,reels u k hk.1,h k hk,h _ (show -k∈baseCube from ⟨by unfold physical; rw [star_neg,hk.1], fun i=> by simpa using hk.2 i⟩)] -- tune
 let R(f:Cover→ℂ)(x:Cover):= (-Complex.I)* f x; have he(f:Cover→ℂ)(p:Summable fun i=>‖f i‖): Summable fun i=>‖R f i‖:=by unfold R; simpa using p -- tune norm
 have hz(f:Cover→ℂ)(i:Momentum):Laurent.read (R f) i=(-Complex.I)*Laurent.read f i:=by unfold Laurent.read; rw [← tsum_mul_left]; apply tsum_congr; intro x; unfold R; simp only [smul_eq_mul]; ring
 have hh:=ht f g p u h; have ha:= ht (R f) (R g) (he _ p) (he _ u) (fun i v=> by rw [hz,hz,h i v]); funext i; apply Complex.ext (congrFun hh i);
 have hp:=congrFun ha i; simpa only [R,reK, neg_mul,Complex.neg_re, Complex.I_mul_re, neg_neg] using hp
lemma shine_move (u:Bool)(j:ℕ)(L M:Side)(p:Odd L.val)(q:Odd M.val) (r:Site L)(a b:SpinIdx) (k:Axis)(D:List Axis)(h:(k::D).length+1≤j):
 Hed u j L M r a b (k::D)=fun x=>Hed u j L M (r+step k) a b D (x-carryStep k r)- Hed u j L M r a b D x:=by
 have hh:D.length+1≤j:=by rw [List.length_cons] at h; omega
 let v:=Hed u j L M (r+step k) a b D; let f:= Hed u j L M r a b D; let Q:=Hed u j L M r a b (k::D); have hx(r):Summable (fun i=>‖Hed u j L M r a b D i‖):= (hubWorld u j L M p q D hh).sumK _ _; let E:= carryStep k r; let Z:= fun x=> v (x-E);
 have ht: Summable fun i:Cover=>‖Z i‖:=by let H:= hx (r+step k); simpa only [Function.comp_def, Equiv.coe_addRight,Z,sub_eq_add_neg] using ((Equiv.addRight (-E)).summable_iff.mpr H)
 have hp:= (ht.of_norm.sub (hx r).of_norm).norm; refine ledger_inj Q _ ((hubWorld u j L M p q _ h).sumK _ _) hp ?_; intro i hk
 have he(X: Cover→ℂ)(p:Summable fun i=>‖X i‖):Summable fun x=> mode i x • X x:=by apply Summable.of_norm; simpa only [norm_smul,mode_real _ _ hk.1,one_mul] using p
 have hz: Laurent.read (fun x=> Z x-f x) i= Laurent.read Z i-Laurent.read f i:=by unfold Laurent.read; rw [← Summable.tsum_sub (he _ ht) (he _ (hx r))]; exact tsum_congr fun i=> by rw [smul_sub]
 have hw: Laurent.read Z i=mode i E * Laurent.read v i:=by unfold Laurent.read; rw [← (Equiv.addRight E).tsum_eq,← tsum_mul_left]; refine tsum_congr fun x=>?_; change mode i (x+E) • Z (x+E)=_; unfold Z; rw [mode_shift, add_sub_cancel_right]; simp only [smul_eq_mul]; ring
 change Laurent.read Q i=Laurent.read (fun x=>Z x-f x) i; rw [hz,hw]; unfold Q v f; rw [shiny u j L M p q (k::D) h i hk,shiny u j L M p q D hh i hk,shiny u j L M p q D hh i hk, enters_H u j L M r p]; rfl
end Thorn
end YM.CF.TableF
end
