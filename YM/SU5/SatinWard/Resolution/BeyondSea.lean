import YM.SU5.SatinWard.Resolution.ClothJ
import YM.CF.Tap.Gamin
import YM.CF.Fock.Line
/-! # Flavor through the scale & common cut, CommGen appointments. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Mezzo
open Function NormedSpace Lattice Laurent Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "V𝕊" => UNI Slot
variable {N P:Side} (G: Ratio N P)
def Circle : Subgroup V𝕊:={
 carrier:= setOf Registrar
 mul_mem':= Registrar.mul
 inv_mem':= Registrar.inv
 one_mem':= Registrar.one }
-- Paid.CONS. enough to use even the χ-projection tests in their intended scope
inductive Concert : V𝕊 → Prop
| one : Concert 1
| trade(a b:V𝕊)(h:Registrar a)(w:Registrar b): Concert (a*b*a⁻¹*b⁻¹)
| adds(a b:V𝕊)(h:Concert a)(w:Concert b) : Concert (a*b)
lemma Concert.gate {g:V𝕊}(h:Concert g) : Registrar g:=by induction h; exact .one; rename_i p t; exact ((p.mul t).mul p.inv).mul t.inv; rename_i p t; exact p.mul t
lemma Concert.inv {g:V𝕊}(h:Concert g) : Concert g⁻¹:=by
 induction h
 · simpa only [inv_one] using Concert.one
 · rename_i a b p t; rw [show (a*b*a⁻¹*b⁻¹)⁻¹=b*a*b⁻¹*a⁻¹ by group]; exact .trade _ _ t p
 rename_i p t; rw [mul_inv_rev]; exact .adds _ _ t p
lemma Concert.star {g:V𝕊}(h:Concert g): Concert (star g):=h.inv

section
variable {I:Type*}[Fintype I][LinearOrder I]
abbrev performance (X: V𝕊 →* UNI I)(g:V𝕊) := acts (quantU (X g)).val
local notation "τ"=> Wave I
lemma performance_add (X:V𝕊→* UNI I)(a b:V𝕊) (x:τ) : performance X (a*b) x= performance X a (performance X b x):=by
 unfold performance; rw [map_mul]; change acts (quant ((X a).val*(X b).val)) _ = _; rw [quant_mul,act_mul]; rfl
lemma performance_one (X:V𝕊→* UNI I)(x:τ): performance X 1 x=x:=by unfold performance; rw [map_one]; change acts (quant 1) x=x; rw [quant_one,act_one] -- arg?
lemma performance_commit (X:V𝕊→* UNI I)(x:τ){k: Op I}(y:IsStarProjection k)(s:Sea k x)
 (u:∀ g:V𝕊,Registrar g→ twist (X g) k=k) (g:V𝕊)(w:Concert g):performance X g x=x:=by
 induction w with
 | one=> exact performance_one ..
 | trade a b p t=>
   have h(j:V𝕊)(v:Registrar j): ∃ c:ℂ,performance X j x=c • x:=by
     have he := s.scalar y (performance X j x); rw [show acts (lineOp k) _ = performance X j x from ?_] at he; swap; ·
          nth_rw 2 [←s.1]; unfold performance; rw [Fock.swivel, ← line_twist, u _ v]
     exact ⟨_,he⟩
   obtain ⟨C,v⟩:=h a p; obtain ⟨D,u⟩:=h b t; obtain ⟨E,w⟩:= h a⁻¹ p.inv; obtain ⟨F,l⟩:=h b⁻¹ t.inv
   have h₁:x≠0:=norm_pos_iff.mp (s.2.symm ▸ zero_lt_one); have hk:= smul_left_injective ℂ h₁
   have h₂:= performance_one X x; have h₃:= h₂
   rw [←mul_inv_cancel a,performance_add,w,map_smul,v,smul_smul] at h₂
   have hz:= hk (show (E*C) • x = (1:ℂ) • x from h₂.trans (by simp))
   rw [←mul_inv_cancel b,performance_add,l,map_smul,u,smul_smul] at h₃
   have hv:= hk (show (F*D) • x = (1:ℂ) • x from h₃.trans (by simp))
   simp only [performance_add,l,map_smul,w,v,u,smul_smul]
   -- regroup
   rw [show F*(E*(D*C))=1 by rw [show F*(E*(D*C))=(E*C)*(F*D) by ac_rfl,hz,hv,mul_one],one_smul]

 | adds a b _ _ ih ih' => rw [performance_add,ih',ih]
end
section
variable (n:Side)
variable {g:V𝕊}(v:Concert g)
lemma roseHead (g:V𝕊)(A:Op SpinIdx) (X:Op Slot):twist (singlet n g) (Tap.headW n A X)=Tap.headW n A (twist g X):=by
 unfold Tap.headW; apply Mir.twist_comm
 rw [←love_coat]
 rw [←map_mul,←map_mul]; congr 1; unfold duet; dsimp only; rw [jump_replicate, jump_replicate]; simp only [op_kron_mul,mul_one]
 rw [show (pal g).val=(1:Op SpinIdx)⊗ₖ g.val from rfl,op_kron_mul,op_kron_mul,one_mul,mul_one, twist_formula, mul_assoc _ (star g.val),g.property.1,mul_one]
lemma roseTick (g:V𝕊):twist (singlet n g) (tickA n)=tickA n:=by
 unfold tickA; rw [Lat.plane_diag]; change twist _ (Tap.headW n (cutM plusHalf) 1)= _; rw [roseHead,map_one]; rfl
include v
lemma roseMate : performance (singlet n) g (mateK n)=mateK n:= performance_commit _ _ (show IsStarProjection (tickA n) from carts_p _ (cutM_idp _)) (tickB n) (fun g _=> roseTick n g) g v
omit n
lemma roseReef : performance (ceremony G) g (basisKet (reefS G true))= basisKet (reefS G true):=by
 let A:= reefS G true; refine performance_commit (ceremony G) (basisKet A) (cutM_idp A) ⟨?_,?_⟩ (fun g _=>by unfold A; rw [←goldLobe,map_mul,map_sub,map_one,lobe_coat,hood_coat]) g v
 · rw [cutLine,cut_basis,if_pos (mem_singleton_self _)]
 simp [basisKet]
end
end YM.CF.Mezzo
