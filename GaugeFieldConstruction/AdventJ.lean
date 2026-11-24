import GaugeFieldConstruction.Marrow
import GaugeFieldConstruction.UmbaraJ
import GaugeFieldConstruction.Brill
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section

open Yoke.Promena CF.Yaw
variable (P:Spine)
local notation "L"=>P.par.R.L
local notation "ℓ"=>P.par.R.L.val
local notation "ξ"=>P.mellow
variable (v:P.VMark)
abbrev ViaJ (T:ℕ → Lattice.Cover):Prop:= ∀ f:ℕ,parentJ P.par.R.L (T (f+1))=T f
abbrev Terrex (s:ℕ)(x:Cover):Prop:=∀ i,(v i:ℝ)=P.mellow s*x i
lemma shell_Terrex :∀ᶠ s:ℕ in atTop,∃ x,Terrex P v s x:=by
 filter_upwards [mint_voxel (P:=P) v] with s ⟨x,hp⟩; subst v; exact ⟨fun i=> ruler P.par.block*x i,fun i=>P.mellow_firm _ _ ⟩
lemma chaseJ (T Q:ℕ→ Lattice.Cover) (a:ℕ) (u:∀ f:ℕ, a≤ f→ parentJ L (T (f+1))=T f)(e:∀ f:ℕ, a≤ f→ parentJ L (Q (f+1))=Q f)(h:∀ᶠ s in atTop,T s=Q s): ∀ s:ℕ,a≤ s→T s=Q s:=by
 intro s d; obtain ⟨f,y,p⟩:=(h.and (eventually_ge_atTop s)).exists
 induction p using Nat.decreasingInduction with
 | self=> exact y
 | of_succ i hs ih=> exact (u i d).symm.trans ((congrArg _ (ih (by omega))).trans (e i d))
lemma terro_exp (s:ℕ)(x:Cover)(j:ℕ)(d:s≤j)(p:Terrex P v s x):Terrex P v j (P.par.R.L.val^(j-s) •x):=by
 intro i; rw[p i,←mellow_age P s j d]
 simp only [Pi.smul_apply,nsmul_eq_mul,Nat.cast_pow,Int.cast_mul,Int.cast_pow,Int.cast_natCast]; ring
local notation "Φ"=>Terrex P v
lemma Terrex.uniq (s:ℕ)(x y:Cover)(p:Φ s x)(q:Φ s y):x=y:=by
 funext i; exact_mod_cast (mul_left_cancel₀ (mellow_good P s).ne' ((p i).symm.trans (q i)))
private lemma parent_p (L₀:Side)(x:Cover):parentJ L₀ (L₀.val • x)=x:=by
 have h: pixJ L₀ (L₀.val • x)=0:=by
    unfold pixJ; have w:wrap L₀ (L₀.val • x)=0:=by funext i; change ((((L₀.val • x:Cover) i:ℤ):ZMod L₀.val))=0; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simp
    rw[w]; funext i; change ZMod.valMinAbs (0:ZMod L₀.val)=0; simp
 have ht:=splitP L₀ (L₀.val • x); rw [h,add_zero] at ht; exact (IsAddTorsionFree.nsmul_right_injective L₀.property.ne') ht -- name tune
abbrev MotionθJ (T:ℕ → Lattice.Cover):Prop:= ViaJ P T ∧∀ i:ℕ,(∃ x,Terrex P v i x)→ Terrex P v i (T i)
lemma road :∃ T, MotionθJ P v T:=by
 let s:= Nat.find (shell_Terrex P v).exists; have ht:∃ x,Terrex P v s x:=Nat.find_spec (shell_Terrex P v).exists
 obtain ⟨x,c⟩:=ht; let T (i:ℕ):Cover:=(parentJ P.par.R.L)^[s-i] (ℓ^(i-s) • x); have he (i:ℕ)(h:s≤ i):T i=ℓ^(i-s) • x:=by unfold T; rw [Nat.sub_eq_zero_of_le h]; rfl
 refine ⟨T,fun f=> ?_,fun i h=>?_⟩
 · by_cases h:f<s
   · unfold T; rw [Nat.sub_eq_zero_of_le (by omega:f+1 ≤ s),Nat.sub_eq_zero_of_le (by omega:f≤ s)]; rw [show s-f=s-(f+1)+1 from by omega,Function.iterate_succ_apply'];
   rw [he _ (by omega), he _ (by omega), show f+1-s=f-s+1 from by omega,pow_succ',mul_smul,parent_p] -- f∉? omega
 have hp:s≤ i:=Nat.find_min' _ h; rw [he i hp]; exact terro_exp _ _ s x i hp c
noncomputable def adventJ (P:Spine)(v:P.VMark):ℕ→ Lattice.Cover := (road P v).choose
lemma keepsJ : MotionθJ P v (adventJ P v) := (road P v).choose_spec
-- physical route displacement at any mesh. gives geometric b price
lemma spale_J (f:ℕ)(i:Axis): |(v i:ℝ) - P.mellow f * adventJ P v f i| ≤ P.mellow f:=by
 let T:=adventJ P v
 obtain ⟨j,hs,p⟩:= ((shell_Terrex P v).and (eventually_ge_atTop f)).exists
 induction p using Nat.decreasingInduction with
 | self=> rw [(keepsJ P v).2 _ hs i,sub_self,abs_zero]; exact (mellow_good P j).le
 | of_succ f hv ih=>
    let L₀:= P.par.R.L.val; let R:=P.mellow f; let K:=P.mellow (f+1)
    have hx: R=K*L₀:= by have v:=mellow_age P f (f+1) (by omega); simp only [Nat.add_sub_cancel_left,pow_one] at v; exact v.symm -- tune
    have he:T (f+1) i=(L₀:ℤ)*T f i + pixJ L (T (f+1)) i:=by
       have q:=splitP L (T (f+1)); rw [(keepsJ P v).1 f] at q; exact (congrFun q i).symm -- mul tune
    have hy:= pinchP L (T (f+1)) i (P.par.R.odd_side);
    have ht: |P.mellow (f+1) * T (f+1) i- R*T f i|≤ R/2:=by
       rw [he,hx]; push_cast; have hw:2*|(pixJ L (T (f+1)) i:ℝ)| ≤ L₀:=by exact_mod_cast hy
       have hz:0<K:= P.mellow_good _
       rw[show _-(K*L₀)*(T f i:ℝ) = K*(pixJ L (T (f+1)) i:ℝ) from (by unfold K; ring),abs_mul,abs_of_pos hz]; linarith only[mul_le_mul_of_nonneg_left hw hz.le]
    have hl:2 ≤ (L₀:ℝ):=by exact_mod_cast (show 2≤L₀ from (by linarith[P.par.R.coarse] : 2 ≤ P.par.R.L.val))
    change |(v i:ℝ) - R*T f i| ≤R; rw [←sub_add_sub_cancel (v i:ℝ) (P.mellow (f+1)*T (f+1) i) (R*T f i)]
    change |(v i:ℝ)- K*(T (f+1) i:ℝ)| ≤K at ih; refine (abs_add_le _ _).trans ((add_le_add ih ht).trans ?_); rw [hx]; linarith only [mul_le_mul_of_nonneg_left hl (show 0 ≤ K from P.mellow_good _|>.le)]
#print axioms road
#print axioms spale_J
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
