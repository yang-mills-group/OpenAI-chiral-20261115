import YM.CF.BPress.Wealth.Void
/-! Each vertical direct cost on its columns (with that leg on the true D face at k=0, not N). its first-order curl and full value, used for strict angular mass and correctly pricing a loss at any severe column.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B) (i:X.Air)
lemma vert_cliff (U: Micro s) (p:∀ i∈X.poles,U i=1) : group.chord (faceValue U (vert X i)) = chord (horizontal (X.depth i.1.1 (i.2.1.val+1)) U (i.1.2,i.2.2)) (horizontal (X.depth i.1.1 i.2.1.val) U (i.1.2,i.2.2)):=by
 rcases i with ⟨⟨t,x⟩,k,l⟩; let τ:= lowTime X t k; change group.chord (travel U (event τ x) (square 0 l.succ)) = _; rw [nq_price]; have hs(i:Tri s): normal τ U i=1:=p _ (X.poles_g _ (low_gaps X t k i)); rw [hs,hs,mul_one,one_mul]; unfold τ; by_cases g:t∈X.dc; · rw [(low_time X t g k).2, (low_time X t g k).1]
 have he := low_before X t (mem_sdiff.mpr ⟨mem_univ _,g⟩) k; rw [he.2, he.1]; exact chord.comm ..

variable (w:Bills X ink)
-- price finite-spacing sums
abbrev dwell {B : BandWidth}: Fin B.D:=⟨0,B.D_pos⟩
def ground {J : Type*}[Zero J](B:BandWidth) (f:Fin B.D→ J)(k:ℕ):J:= if k=0 then 0 else if h:k-1<B.D then f ⟨k-1,h⟩ else 0
lemma ground_succ {J : Type*}[Zero J](B:BandWidth)(f:Fin B.D →J)(p:Fin B.D): ground B f (p.val+1)=f p:=by simp [ground,p.isLt]
lemma ground_zero {J : Type*}[Zero J](B:BandWidth)(f:Fin B.D→J) : ground B f 0=0:=by simp [ground]
def past (x:X.Air):= ground B (fun k=> w (x.1,k,x.2.2)) x.2.1.val
lemma form_vertical (R:PathData group)(M:ℕ):
    form R M (.inl (vert X i)) (canon X w)= if i.1.1∈X.dc then w i- past X w i else past X w i - w i:=by
 obtain ⟨⟨t,x⟩,k,l⟩:=i; let τ := lowTime X t k; let u :X.Air:= ((t,x),k,l); let Q:=canon X w; rw [form]; dsimp only [Sum.elim_inl]; rw [orbitP_id]; have v(t : Per s)(x:Tri s): Q (vl t x)=0:= none_key X w (EdgeKey_V X t x); have e(z:Fin B.D): Q (fl (X.depth t (z.val+1)) (x,l))= w ((t,x),z,l):= pay_key X w (key_depth X ((t,x),z,l)); have he(k)(h:k ≤ B.D) : Q (fl (X.depth t k) (x,l))=ground B (fun k=>w ((t,x),k,l)) k:= by
    cases k with
    | zero=> rw [ground_zero]; exact none_key X w (key_o X t (x,l))
    | succ k=>
       rw [e ⟨k,h⟩] -- tune rw annotation
       exact (ground_succ B (fun k=> w ((t,x),k,l)) ⟨k,h⟩).symm
 unfold circle; simp only; change Q (vl τ x)+Q (event τ x+step 0,l.succ) - Q (event τ x+step l.succ,0) - Q (fl τ (x,l))= if t∈ _ then w u - _ else _-w u; rw [event_up, event_across]; change Q (vl τ x)+Q (fl (τ+1) (x,l))-Q (vl τ (glide l x))-_= _; rw [v,v,zero_add,sub_zero]; unfold τ; split; next h=> rw [(low_time X t h k).2,(low_time X t h k).1, e k,he k.val k.isLt.le]; rfl
 next h=> have Z:= low_before X t (mem_sdiff.mpr (show t∈ (univ: Finset X.Index) ∧ _ from ⟨mem_univ _,h⟩)) k; rw [Z.2,Z.1,e k,he k.val k.isLt.le]; rfl
lemma v_norm (R:PathData group)(M:ℕ): ‖form R M (.inl (vert X i)) (canon X w)‖= ‖w i-past X w i‖:=by rw [form_vertical]; split; rfl; exact norm_sub_rev ..

-- Massive lower budget per column
abbrev point (B:BandWidth)(f:Fin B.D→ ink)(i:Fin B.D):= f i-ground B f i.val
def verticalE (B:BandWidth)(f:Fin B.D→ ink) := ∑ i: Fin B.D, ‖point B f i‖^2
lemma costsD (B:BandWidth)(f:Fin B.D→ ink)(i:Fin B.D): ‖f i‖^2 ≤ (B.D:ℝ)^2 * verticalE B f := by
 let p:=verticalE B f; have hx:0 ≤ p:=by unfold p verticalE; positivity
 let q:=Real.sqrt p; have v:q^2=p:=Real.sq_sqrt hx; have ht:0≤q:=Real.sqrt_nonneg p
 have he(i:Fin B.D): ‖point B f i‖ ≤ q:= by apply (sq_le_sq₀ (norm_nonneg _) ht).mp; rw [v]; exact single_le_sum (f:=fun i=>‖point B f i‖^2) (fun i _=>sq_nonneg _) (mem_univ i); -- tune
 have hp(i:ℕ)(t:i≤B.D): ‖ground B f i‖ ≤ i*q:=by
    induction i with
    | zero=> simp [ground_zero]
    | succ k ih=>
       let u:Fin B.D:=⟨k,t⟩; have hv:= norm_le_norm_sub_add (f u) (ground B f k); refine le_trans ?_ (hv.trans ?_); swap; · refine le_trans (add_le_add (he u) (ih (by omega))) (Eq.le ?_); push_cast; ring
       rw [show k=u.val from rfl, ground_succ]
 have h := hp (i.val+1) i.isLt; rw [ground_succ] at h; change _≤ (B.D:ℝ)^2*p; rw [← v,←mul_pow]; gcongr ?_ ^ 2; refine le_trans h ?_; gcongr; exact_mod_cast i.isLt
end YM.CF.BPress.Wealth
