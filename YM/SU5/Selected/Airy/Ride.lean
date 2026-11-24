import YM.SU5.Selected.Airy.Payment
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
variable (n p:ℕ)(G:Side)(g:8≤G.val)(e:n≥4)
local notation "V"=> plinth G n p e
local notation "Y"=> artisans G n p e
local notation "Fp"=>children G n p
local notation "W" a:max => collage n p G e a
local notation "ρ"=> Real.exp (-(1/2))
private def soapPiece (S:Finset (Fin 3))(w:Coast):Op (Fin p):=(∏ i∈S, (↑(chart G (w i.castSucc)):ℂ)^2) • 1
include g
private lemma soap_piece (S: Finset (Fin 3))(i:Fin 3)(h:i∉S): raiser G i.castSucc (soapPiece p G (insert i S))= soapPiece p G S:=by
 funext w; let f(a:Fin 3)(u:Coast):ℂ:= ↑(chart G (u a.castSucc));
 let A:ℂ:=∏ a∈ S,f a w^2; have h₀(s:ℕ): soapPiece p G (insert i S) (raised G i.castSucc s w)= f i (raised G i.castSucc s w)^2 • soapPiece p G S w:=by
    unfold soapPiece; rw [←mul_smul,prod_insert h]; apply congrArg (· • (1:Op (Fin p))); congr 1
    apply prod_congr rfl; intro j b; rw [raised,Pi.add_apply,Pi.single_eq_of_ne (show j.castSucc ≠ i.castSucc from fun g=>h ((Fin.castSucc_injective _ g) ▸ b)),add_zero]
 rw [raiser]; simp_rw [Pi.smul_apply,Finset.sum_apply,Function.comp,h₀,←Finset.sum_smul,smul_smul]; let r:=G.val
 have ht(s:ℕ): f i (raised G i.castSucc s w)^2=(↑((chart G (w i.castSucc+s • tier G))^2):ℂ):=by unfold f raised; simp
 simp_rw [ht,←Complex.ofReal_sum, stack_price G g]; push_cast; rw [inv_mul_cancel₀ (side_ne _), one_smul]
lemma trex : raiser G 0 (raiser G 1 (raiser G 2 (solvent p G)))= (fun (_:Coast)=> (1: Op (Fin p))):=by
 have he:solvent p G= soapPiece p G univ:=by ext1 w; unfold solvent soapPiece; congr 1; unfold soap; push_cast; exact prod_pow .. |>.symm -- tune
 let c_i:= @Fin.castSucc 3
 change raiser G (c_i 0) (raiser G (c_i 1) (raiser G (c_i 2) _))=_
 rw [he,show (univ: Finset (Fin 3)) = insert 2 (insert 1 (insert 0 ∅)) by decide];
 unfold c_i
 iterate 3 rw [soap_piece p G g _ _ (by decide)]
 unfold soapPiece; simp
local notation "Xv"=> raiser G 2
local notation "Yv"=> raiser G 1
local notation "Zv"=> raiser G 0

theorem payment : ∃ K:ℝ,0<K∧∀ (D:Side)(w:Coast), ‖Zv (Yv (Xv (raiser D 3 (collage n p G e)))) w-1‖≤ K*ρ^D.val :=by
 obtain ⟨K,hp,h⟩:= raises_time n p G g e -- shadow p fix
 refine ⟨K,hp,fun D w=>?_⟩; let x:=raiser D (3:Axis) (collage n p G e); let y:=solvent p G; have ht:= raise_hold (R:=K*ρ^D.val) (F:=x-y) (h D); have he(v):‖Zv (Yv (Xv (x-y))) v‖ ≤ K * ρ^D.val:= raise_hold (raise_hold (ht G 2) G 1) G 0 v -- infer
 have he:=he w; simp_rw [raise_sub] at he; unfold x y at he; rwa [Pi.sub_apply,trex _ G g] at he

variable {v:Type*}[Fintype v][DecidableEq v]{N:Side}(D:Side)(x:v→Site N ×Fin p)
structure Beacons (G D:Side){v : Type*}{N:Side}(p:ℕ) (x:v→ Site N × Fin p) : Prop where
 mono:Injective x
 spanX:G.val∣N.val
 spanT:D.val∣N.val
 row(v'): ∀ i:Fin 3,G.val∣ ((x v').1 i.castSucc).val
 col(v'): D.val∣ ((x v').1 3).val
variable (h:Beacons G D p x)
omit g
include h
lemma beam_enact (F:Coast→ Op (Fin p)) : (mask x)ᴴ* freeze ((Zv (Yv (Xv (raiser D 3 F)))) ∘ brim N)*mask x=(mask x)ᴴ *freeze (F ∘ brim N)*mask x:=by
 rw [tightrope G h.spanX x 0 (fun a=>h.row a 0),tightrope G h.spanX x 1 (fun a=> h.row a 1), tightrope G h.spanX x 2 (fun a=> h.row a 2),tightrope D h.spanT x 3 h.col]
omit h
-- Any number of input columns & any spatial period. choose all. exact no log B.
include g
lemma coin : ∃ K:ℝ,0<K ∧∀ {v:Type}[Fintype v][DecidableEq v],∀ (N D:Side)(x:v→ Site N×Fin p), Beacons G D p x → ‖(freeze (Fp ∘ brim N) * mask x)ᴴ * (freeze (Y ∘ brim N) * mask x)-1‖ ≤ K*ρ^D.val:=by
 obtain ⟨K,h,e'⟩:= payment n p G g e; refine ⟨K,h,fun {_} _ _ N D x v₀=>?_⟩
 let F:= collage n p G e; let V':= Zv (Yv (Xv (raiser D 3 F))); let m:=mask x
 have ht:(fun (_:Site N)=> (1:Op (Fin p)))=1:= rfl
 let X:=V' ∘ brim N-(1: Site N→Op (Fin p))
 have hG:‖freeze X‖≤ K*ρ^D.val:= freeze_norm (by positivity) (fun u=> e' D (brim N u))
 have hc: (freeze (Fp ∘ brim N)*m)ᴴ*(freeze (Y ∘ brim N)*m)-1=mᴴ*freeze X*m:=by
    unfold X; rw [freeze_sub, ←ht,freeze_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one, mask_self x v₀.mono]; unfold V'; rw [beam_enact p G D x v₀ F]; rw [Matrix.conjTranspose_mul,freeze_star,Matrix.mul_assoc,← Matrix.mul_assoc (freeze _),freeze_mul]; rw [Matrix.mul_assoc mᴴ]; rfl
 have he: ‖m‖ ≤ 1:= mask_toll x v₀.mono; unfold m at *; rw [hc]; apply (Matrix.l2_opNorm_mul ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) he).trans; apply (Matrix.l2_opNorm_mul ..).trans; rw [Matrix.l2_opNorm_conjTranspose]; exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hG
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms payment
#print axioms beam_enact
#print axioms coin
