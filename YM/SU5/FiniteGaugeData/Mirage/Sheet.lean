import YM.SU5.FiniteGaugeData.Largo.Duet
import YM.SU5.FiniteGaugeData.Brique.Bolt
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
-- pair transmute two family flavors (same chiral shape). use ALL σ color on LEFT ring (universal covariance), pin ONE color on right ring (til after global average; each nonconstant term at least one center σ-charge even beyond one creator at same site). Matrix discount later. 
open SU
variable (α β : Fin 3) (Y: Finset Sheet) (u v:Sheet)(e:SU.E)
abbrev genre (σ:Window.Family): Finset Sheet:= univ.filter fun i: Sheet=> i.isLeft=σ.2
lemma genre_color (x:SU.Slot): x∈ colors σ ↔ x.1=σ.1 ∧ x.2∈ genre σ:=by simp only [genre,colors,mem_filter,mem_univ,true_and,family]; exact Prod.ext_iff
lemma genre_card : (genre σ).card=dimf σ:=by obtain ⟨s,b⟩:=σ; cases b <;> fin_cases s <;> decide
lemma genre_sum : (genre σ).card ≤ 45:=by rw [genre_card]; unfold dimf; split <;> omega
lemma paid_any (σ:Window.Family): (genre σ).Nonempty:= card_pos.mp (by rw [genre_card]; unfold dimf; split <;> omega)
abbrev tint (Y:Finset Sheet)(α:Fin 3): Finset SU.Slot:= {α}×ˢ Y
def piggy (U:Finset (Mini N))(Y:Finset Sheet)(α:Fin 3) : Finset (Single N):= U ×ˢ tint Y α
local notation "W₀" => fun (U:Finset (Mini N)) => piggy U Y α
lemma pigU : piggy (WalU N S) Y α ⊆ Tset N:=fun i t=> (grade_one ..).mpr ((mem_product.mp (mem_product.mp t).1).2)
lemma pigL : piggy (WalL N S) Y α ⊆ (Tset N)ᶜ:= fun i t=> Finset.mem_compl.mpr (mt (grade_one _ _|>.1) (mem_compl.mp (mem_product.mp (mem_product.mp t).1).2))
lemma piggin (V:Finset (Mini N)): (piggy V Y α).card= V.card*Y.card:= by simp [piggy,tint]
-- cap rank.V ≤ constants. each color <=45.
lemma pinW(v:ℕ)(U:Finset Cover)(Y:Finset Sheet)(α:Fin 3)(k:(WalU N U).card≤v)(t:Y.card≤45): (piggy (WalU N U) Y α).card ≤ v*45:=by rw [piggin]; gcongr
abbrev αslot (b:Sheet)(i:Fin 3): SU.Slot:= (i,b)
def Exhibit (Y:Finset Sheet)(a b: Fin 3): Op Slot:= (Matrix.single b a 1) ⊗ₖ cutM Y -- maps a→b same rep flag chosen; a needn't distinct
lemma expo (k j: Slot) : Exhibit Y α β k j= if k.1=β∧ j.1=α ∧ k.2=j.2 ∧ k.2∈Y then 1 else 0:=by
 unfold Exhibit; rw [Matrix.kronecker_apply]; by_cases p:k.1=β <;> by_cases g:j.1=α <;> by_cases z:k.2=j.2 <;> by_cases h:k.2∈Y <;> simp [p,g,z,h,cutM, eq_comm,Matrix.single_apply,tint] <;> grind -- orientation
lemma Expo_comm : Commute (Exhibit (genre σ) α β) (matter e).val:=by
 have he:Commute (cutM (genre σ)) (SU.each (fund e)):=cutSpan_comm _ _ fun i j t=>by
    have hx: family (α,i)=family (α,j):=by
        by_contra f; apply t; have hu:= neq_block e f; change (triple (fund e)) (α,i) (α,j)=_ at hu; simpa [triple] using hu
    simp [genre,show i.isLeft=j.isLeft from congrArg Prod.snd hx]
 change _*(triple (fund e))= (triple (fund e))*_; unfold Exhibit triple; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,he.eq]
lemma expo_id : star (Exhibit Y α β)*Exhibit Y α β=cutM (tint Y α):=by
 ext i j; rw [Matrix.mul_apply, sum_eq_single (αslot i.2 β)];
 · simp_rw [Matrix.star_apply,expo]; by_cases h:i=j; · subst j; simp only [αslot,cutM,Matrix.diagonal_apply_eq,tint,mem_product,true_and,mem_singleton]; split_ifs <;> simp
   have ht:i.1≠α ∨ j.1≠α ∨ i.2≠j.2:=by
    by_contra! z; exact h (Prod.ext (z.1.trans z.2.1.symm) z.2.2)
   rw [cutM,Matrix.diagonal_apply_ne _ h]; rcases ht with w|w|w <;> simp [w]
 · intro b _ p; rw [Matrix.star_apply,expo]; rw [if_neg (fun t=> p (Prod.ext t.1 t.2.2.1)),star_zero, zero_mul]; -- okay
 simp
lemma exhibit_n (v:α≠β): αslot u α≠αslot u β:=fun h=> v (congrArg Prod.fst h)
variable {P:Op (Mini N)} {Z:Op Slot}
def cibe (V:Op (Mini N))(α β: Fin 3)(Y:Finset Sheet): Op (Single N):= V ⊗ₖ Exhibit Y α β
lemma matter_c (e:SU.E): (tradew N (globalH N e)).val= (1:Op (Mini N)) ⊗ₖ (matter e).val:=by ext i j; unfold tradew; simp_rw [jump_apply,Equiv.refl_apply]; simp only [Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.kronecker_apply,ite_mul,one_mul,zero_mul]; rfl -- tune
lemma matterSpin (Z:Op (Mini N)): twist (tradew N (globalH N e)) (cibe Z α β (genre σ))= cibe Z α β (genre σ):= by apply Mir.twist_comm; rw [matter_c]; unfold cibe; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,(Expo_comm ..).eq] -- arguments v check
lemma norm_k₀ : ‖P ⊗ₖ (1:Op Slot)‖ ≤ ‖P‖ := by
 let s:=Equiv.prodComm (Mini N) Slot; let A:=jump (Equiv.refl Slot) (fun _=>P); let U:=grip s.symm (fun _=>1); have he:Uᴴ* U=1:= grip_clean _ _ s.symm.injective fun _=> by simp;
 rw [show P ⊗ₖ (1:Op Slot)= U*A*Uᴴ from ?_]; · exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((Matrix.l2_opNorm_conjTranspose ..).trans_le (grip_pay _ he))).trans ((Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (grip_pay _ he)).trans (jump_bound _ _ (norm_nonneg _) (fun i=> le_rfl)))))
 ext i j; -- formulas U* not grip_off when f invert. change U=star grip.C
 let X:=grip s (fun _=> (1:ℂ)); have he: U=Xᴴ:=by unfold U X; ext i j; simp only [Matrix.conjTranspose_apply,grip,Matrix.of_apply,apply_ite star,star_zero,star_one,s.eq_symm_apply]; simp [eq_comm]
 rw [he,Matrix.conjTranspose_conjTranspose,on_grip,grip_off]; unfold A; rw [jump_apply,star_one]; simp only [Matrix.kroneckerMap_apply,Matrix.one_apply, Equiv.refl_apply, s,Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap]; split <;> simp_all
lemma normVisit: ‖Exhibit Y α β‖ ≤ 1:=by let V:= Exhibit Y α β; rw [←sq_le_sq₀ (norm_nonneg _) (by norm_num),sq, ←Matrix.l2_opNorm_conjTranspose_mul_self]; rw [← Matrix.star_eq_conjTranspose,expo_id,one_pow]; exact cutBud _
lemma breathe (P:Op (Mini N)): ‖cibe P α β Y‖ ≤ ‖P‖:=by
 let Z:= Exhibit Y α β; let Q:= (1:Op (Mini N)) ⊗ₖ Z; have he: ‖Q‖ ≤ 1:= (replicas_bound ..).trans (normVisit α β Y)
 rw [show cibe P α β Y=(P ⊗ₖ (1:Op Slot))*Q from ?_]; · exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) he).trans norm_k₀)
 unfold Q; rw [op_kron_mul,one_mul,mul_one]; rfl
lemma fFlat (M:Tulip.Male): funde 4 M N 1= flatH M N ⊗ₖ 1:= by
 rw [funde_flat 4 (by omega) M N, show cart N (tub (bar 4 M.val))=plates N (bar 4 M.val) from cart_traded (A:=bar 4 M.val) (cBar 4 M.val true (by omega) M.property) N]
lemma pig_cutT {I: Finset (Mini N)} (h:P*cutM I=P): cibe P α β Y * cutM (piggy I Y α) = cibe P α β Y:=by
 ext i j; rw [Largo.compass']; by_cases t:j∈ piggy I Y α; rw [if_pos t]; rw [if_neg t]; unfold cibe; rw [Matrix.kroneckerMap_apply, expo]; split; next v=> have hv:j.1∉ I:=fun s=>t (mem_product.mpr ⟨s,mem_product.mpr ⟨mem_singleton.mpr v.2.1, v.2.2.1 ▸ v.2.2.2⟩⟩); nth_rw 1 [←h]; rw [Largo.compass',if_neg hv,zero_mul]
 rw [mul_zero]
lemma pig_cutV {I: Finset (Mini N)} (h:cutM I*P=P): cutM (piggy I Y β) * cibe P α β Y= cibe P α β Y:=by
 ext i j; rw [Largo.compass]; by_cases t:i∈ piggy I Y β; rw [if_pos t]; rw [if_neg t]; unfold cibe; rw [Matrix.kroneckerMap_apply, expo]; split; next v=> have hv:i.1∉ I:=fun s=>t (mem_product.mpr ⟨s,mem_product.mpr ⟨mem_singleton.mpr v.1,v.2.2.2⟩⟩); nth_rw 1 [←h]; rw [Largo.compass,if_neg hv,zero_mul]
 rw [mul_zero]
-- single-slot functor. on u if diff. needed zero interference
local notation "Π" => (Tset N)
def Channel(N:Side)(v:Slot): Ruler (Single N) (Mini N):= grip (fun x=>(x,v)) (fun _=>1)
lemma Channelθ (v:Slot): (Channel N v)ᴴ*Channel N v=1:= grip_clean _ _ (fun _ _ h=>congrArg Prod.fst h) fun _=>by simp
lemma Channelψ (v:Slot): cutM (Tset N)*Channel N v=Channel N v*cutM (ruddy N):=by
 ext i j; rw [Largo.compass,Largo.compass']; by_cases h:i=(j,v); · subst i; unfold Channel; simp only [grip,Matrix.of_apply,ruddy, mem_product,mem_univ,true_and]; simp [show (j,v)∈Tset N ↔ j.2∈plusHalf from grade_one .. ]
 simp [Channel,grip,h]
lemma Channelι (v:Slot): cutM (Tset N)ᶜ*Channel N v=Channel N v*cutM (scel N):=by
 rw [show cutM (scel N) =1-cutM (ruddy N) by rw [←cutM_read' (ruddy N)]; unfold scel; abel]; rw [show cutM (Tset N)ᶜ=1-cutM (Tset N) from ?_, Matrix.mul_sub,Matrix.sub_mul,Channelψ,Matrix.mul_one,Matrix.one_mul]; rw [←cutM_read' (Tset N)]; abel
lemma Channel_z (s v:Slot)(z:s≠v) : (Channel N s)ᴴ*Channel N v=0:=by unfold Channel; ext i j; rw [grip_off,grip]; simp [z]
lemma ChannelGl(V:Op (Mini N))(v:Slot): (V ⊗ₖ (1:Op Slot)) * Channel N v=Channel N v*V:=by ext ⟨i,y⟩ j; unfold Channel; rw [on_grip,Matrix.mul_apply]; by_cases h:v=y <;> simp [h, Ne.symm, grip,Matrix.one_apply,ite_mul, eq_comm, mul_ite] -- tune
lemma Channel_s {P:Op (Mini N)} (h:u∈Y): cibe P α β Y * Channel N (αslot u α)=Channel N (αslot u β)*P:=by unfold Channel cibe; ext ⟨i,j,y⟩ k; rw [on_grip,Matrix.mul_apply]; by_cases h':j=β <;> by_cases z:y=u <;> simp [h',z,grip,ite_mul, αslot,expo, h]; -- tune
lemma Channel_v {P:Op (Mini N)}(u:α≠β)(v:Fin 3)(w:Sheet): cibe P α v Y * Channel N (αslot w β)=0:=by unfold Channel cibe; ext i j; rw [on_grip,Matrix.kroneckerMap_apply]; simp [expo, u,Ne.symm u, αslot]
end YM.CF.Window.Mirage
