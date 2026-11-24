import YM.CF.BPress.Pf.Wick
/-! Wick quotient, Pf recursion, and trace/spectral Ward inputs. Include even archiveP scaling function budget if needed, all on the SAME arrangements. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter Finset NormedSpace Fock Spin Spin.Cellar Spin.Cellar.Pass Pledge Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{A B L C:Op I}{c d r:ℝ}{P Q:Finset I}
variable (F:Arrange P Q L A C c r){u: Wave I}(H: Top A u)
abbrev strap {α:Type*}(X Y:α → Op I)(i:α → I) (j: List α) :FC I:= (j.map fun l=> introW (X l) (Y l) (i l)).prod
abbrev valueL {α:Type*}(B k:Wave I)(X Y:α→Op I)(i:α→I)(t:List α):= wick B k (strap X Y i t)
section

local notation "uWave" => braC P Q C
local notation "archiveP" => cutM P
local notation "quP" => cutM Q
include H F
theorem recursion {α:Type*}(X Y:α→Op I)(i:α→I)(l:List α)(x:α): let κ(b:α):= contextM archiveP quP L A C (X x) (Y x) (X b) (Y b) (i x) (i b);
 valueL uWave u X Y i (x::l) = dues κ (valueL uWave u X Y i) [] l :=by
 intro κ; let S:=introW (X x) (Y x) (i x); let G:=strap X Y i; let v:=introW (fitP archiveP quP L A C (X x) (Y x)) (fitW archiveP quP L A C (X x) (Y x)) (i x)
 obtain ⟨hv,hz⟩:= annih F H (X x) (Y x) (i x)
 change wick uWave u (S*G l)= _; rw [show wick uWave u (S*G l)=wick uWave u (v*G l) from ?_]; swap; · have he:= wick.lt0 (k:=u) hz (G l); rw [sub_mul,wick.sub] at he; exact sub_eq_zero.mp he
 suffices hx :∀t J: List α, wick uWave u (G J*(v*G t))= dues κ (valueL uWave u X Y i) J t by simpa [G,strap] using hx l []
 intro t J; induction t generalizing J with
 | nil=> simpa only [G,strap,List.map_nil,List.prod_nil,mul_one,dues,fee] using wick.rt0 hv (G J)
 | cons j t ih=>
    let T:=introW (X j) (Y j) (i j); rw [show G (j::t)=T*G t from rfl,←mul_assoc v T,show v*T= κ j • 1-T*v from eq_sub_of_add_eq (CAR_fitC (X x) (Y x) (i x) (X j) (Y j) (i j)),sub_mul,mul_sub]; rw [wick.sub,Algebra.smul_mul_assoc,one_mul,Algebra.mul_smul_comm, wick.termScale, mul_assoc T, ←mul_assoc (G J), show G J*T=G (J++[j]) by unfold G strap T; rw [List.map_append,List.prod_append]; simp, ih]
    simp only [dues,fee]; rw [show valueL uWave u X Y i (J++t)=wick uWave u (G J*G t) from (by unfold G valueL strap; rw [List.map_append,List.prod_append])]
lemma baseL {α:Type*}(X Y:α→Op I)(i:α→I): valueL uWave u X Y i []=1:= wick.one (F.realP H)
local notation "κ" => (contextM archiveP quP L A C)
lemma bare_one' (i:I):introW (1:Op I) 0 i=put i:= by unfold introW letters letterV; simp [remove]
-- determinant trace Wick formulas
lemma powers_t(T:Op I)(S R X Y:Op I): wick uWave u (dyad T (introW S R) (introW X Y))=(T * (κ S R X Y)ᵀ).trace := by
 unfold dyad; simp_rw [wick.termSum, wick.termScale, frameC F H S R]; exact (by simp [Matrix.trace,Matrix.mul_apply,Matrix.diag])
lemma bare(T:Op I): wick uWave u (dg T)=(T*(κ 1 0 0 1)ᵀ).trace:=by
 unfold dg; rw [show put= introW (1:Op I) 0 from (funext fun i=> (bare_one' F H i).symm),show takeF=introW (0:Op I) 1 from Eq.symm (funext (fun i=> by unfold introW letters letterV; simp [Fock.remove_take]))]; exact powers_t F H T _ _ _ _
-- derivative of the adjoint path in bra orientation.
lemma couple(T:Op I): wick uWave u (star (coupl T))=(2:ℂ)⁻¹*(star T*(κ 0 1 0 1)ᵀ).trace:=by
 have he: star (coupl T)=(2:ℂ)⁻¹ • dyad (star T) (introW 0 1) (introW 0 1):=by
    rw [coupl,star_smul]; congr 1; norm_num; unfold squareP dyad; rw [sum_comm]; simp_rw [star_sum,star_smul,star_mul]; have hp(i:I) : introW (0:Op I) 1 i=takeF i:= by simp [introW,letters,letterV]
    simp_rw [hp]; rfl
 rw [he,wick.termScale,powers_t F H]
end
lemma in_norm (b k' b' k: Wave I)(F:FC I)(r s:ℂ)(u:r≠0)(v:s≠0)(h:b'=r • b)(k0:k'=s • k) : wick b' k' F=wick b k F:=by
 rw [h,k0]; simp only [wick,map_smul,inner_smul_left,inner_smul_right]; have hp: (starRingEnd ℂ) r≠0:=by simpa
 rw [mul_div_mul_left _ _ v,mul_div_mul_left _ _ hp]
lemma pureE (C:Op I): braC ∅ ∅ C=pairWave C:=by
 rw [braC, show occupy (∅:Finset I) ∅=1 from (by ext; simp [occupy,cutM,light, Matrix.diagonal_apply,Matrix.one_apply]),act_one]
section price
open Spin.Pledge
lemma contexts_budget (P Q L A C M:Pledge)(p:0<c)(v:0≤d)(r:ℝ)(h:0≤r)(u:r<1) :∃ W:Pledge,∀ {I D Y:Type}[Fintype Y][DecidableEq Y][Fintype I][LinearOrder I][Nonempty I][TopologicalSpace D]{b:Stage Y I D Empty}{T K:D→Finset I}{S uWave J: Raw D I}, Capacity b d→P.Costs b (fun i=> cutM (T i))→Q.Costs b (fun i=>cutM (K i))→L.Costs b S→A.Costs b uWave→C.Costs b J→ (∀ x, Arrange (T x) (K x) (S x) (uWave x) (J x) c r)→ ∀{X Y' E Z: Raw D I}, M.Costs b X→M.Costs b Y'→M.Costs b E→M.Costs b Z→ W.Costs b (fun i=> contextM (cutM (T i)) (cutM (K i)) (S i) (uWave i) (J i) (X i) (Y' i) (E i) (Z i)) :=by
 obtain ⟨W,w⟩:= Serve.price_all P Q L A C M p v r h u; let T:= W.times M; refine ⟨T.plus T,?_⟩; intro I D Y _ _ _ _ _ _ b X Y' S uWave J z archiveP b₀ c d e Q X₁ X₂ X₃ X₄ t₁ t₂ t₃ t₄; have ht:=w z archiveP b₀ c d e (fun x=>(Q x).gap) (fun x=>(Q x).skit) (fun x=>(Q x).backB) t₁ t₂; exact Costs.plus (Costs.mul (Costs.transpose ht.2) t₃) (Costs.mul (Costs.transpose ht.1) t₄)
end price
end YM.CF.BPress.Pf
