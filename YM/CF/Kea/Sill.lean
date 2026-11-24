import YM.CF.Kea.Mant
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev Stag(N:Side):=Site N × Slot
abbrev Bri(N:Side):=Stag N × SpinIdx
def budE(N:Side):Single N ≃ Bri N := (helix N).trans ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans (Equiv.prodAssoc ..).symm)
def bel(N:Side):Op (Bri N)≃⋆ₐ[ℂ] Op (Single N):={ Matrix.reindexAlgEquiv ℂ ℂ (budE N).symm with map_star' _:=rfl, map_smul' a b:=rfl }
def arch(A:Stag N→ Op SpinIdx):Op (Single N):=bel N (jump (Equiv.refl _) A)
lemma arch_a(A B:Stag N→Op SpinIdx):arch (A+B)=arch A+arch B:=by rw [arch,jump_add,map_add]; rfl
lemma arch_m(A B:Stag N→Op SpinIdx):arch (A*B)=arch A*arch B:=by unfold arch; rw [← map_mul,jump_mul]; rfl
lemma arch_s(A:Stag N→Op SpinIdx):arch (star A)=star (arch A):=by unfold arch; rw [← map_star,jump_star]; rfl
lemma arch_one: arch (1:Stag N→Op SpinIdx)=1:=by change bel N (jump _ (fun _=>1))=_; rw [show jump _ _=(1:Op (Bri N)) from jump_id,map_one]
lemma arch_at(A: Stag N→Op SpinIdx)(x y: Single N):arch A x y= if x.1.1=y.1.1 ∧ x.2=y.2 then A (x.1.1,x.2) x.1.2 y.1.2 else 0:=by change (if (x.1.1,x.2) = (y.1.1,y.2) then _ else _)=_; simp; rfl
-- spin Fourier, reference plane. no color permutation in U
abbrev wedgeN(N: Side): Op (Single N):= love N (spatialU N Slot).val
def colU (N:Side): UNI (Single N):=⟨wedgeN N, by
 constructor
 · unfold wedgeN; rw [← map_star, ←map_mul,(spatialU N Slot).property.1,map_one]
 unfold wedgeN; rw [← map_star, ←map_mul,(spatialU N Slot).property.2,map_one]⟩
lemma coil(x y: Single N): (colU N).val x y= if x.1.2=y.1.2 ∧ x.2=y.2 then Fourier N x.1.1 y.1.1 else 0:=by change Fourier N x.1.1 y.1.1 * (1:Op (SpinIdx×Slot)) (x.1.2,x.2) (y.1.2,y.2)=_; simp only [Matrix.one_apply]; by_cases h:x.1.2=y.1.2 ∧ x.2=y.2 <;> simp [h]
lemma wool(A:Stag N→Op SpinIdx)(x y:Single N) : ((colU N).val* arch A) x y= if x.2=y.2 then Fourier N x.1.1 y.1.1*A (y.1.1,y.2) x.1.2 y.1.2 else 0:=by
 rw [Matrix.mul_apply]; simp_rw [coil,arch_at]
 rw [sum_eq_single ((y.1.1,x.1.2),y.2)]
 · by_cases p:x.2=y.2 <;> simp [p]
 · rintro ⟨⟨j,i⟩,u⟩ h p; split_ifs with l v w <;> simp_all
 simp
lemma on_a(c:ℝ)(A:Stag N→Op SpinIdx):arch (c • A)=c • arch A:=by ext x y; by_cases h:x.1.1=y.1.1∧x.2=y.2 <;> simp [arch_at,h]
def setX(N:Side): (Stag N→Op SpinIdx)→ₐ[ℝ] Op (Single N):= AlgHom.ofLinearMap { toFun:=arch,map_add':=arch_a,map_smul':=fun a b=> on_a a b } arch_one arch_m
def Dofu(N:Side): (Stag N→Op SpinIdx) →ₐ[ℝ] Op (Single N):= (twist (colU N)).toAlgEquiv.toAlgHom.comp (setX N)
lemma Dofu_s(A:Stag N→Op SpinIdx):Dofu N (star A)=star (Dofu N A):=by change twist _ (arch _)=star (twist _ (arch A)); rw [arch_s,map_star]
lemma turnU(V:Op SpinIdx): love N (spin N Slot V)=Dofu N fun i=> V:=by
 rw [twist_bands_spin]; change love N (twist _ _)=twist (colU N) (arch _); rw [twist_formula,twist_formula,map_mul,map_mul,map_star]; change (colU N).val*_ *_=_; rw [show love N (bands Slot (fun _=>V))=arch (N:=N) (fun _=>V) from ?_]
 · rfl
 ext ⟨⟨x,i⟩,b⟩ ⟨⟨y,j⟩,c⟩; rw [arch_at]
 change bands (N:=N) Slot (fun _=>V) (x,i,b) (y,j,c)=_; by_cases h:x=y <;> by_cases g:b=c <;> simp [g,h,bands,jump_apply,Matrix.one_apply]

-- momentum shifted by matter weights; reduction per color. calendar
structure Slide(N:Side)(x:Candle) where
  u:Slot → Offset N
  z:Slot→ Cover
  f(i): rise x i= (u i).val+ fun j=> 2*pinch N*(z i j)
def skim(N:Side)(x:Candle): Slide N x:=Classical.choice <| by choose u z p using (fun i=> moved N (rise x i)); exact ⟨⟨u,z,p⟩⟩
variable {x:Candle}
def angle(S:Slide N x)(i:Stag N):Bin:= pm (i.1+wrap N (S.z i.2)) +(S.u i.2).val
lemma peer_p(S:Slide N x)(i:Stag N):peers (pm i.1+rise x i.2) (angle S i):=by rw [S.f, add_comm (S.u i.2).val,← add_assoc]; exact (tap_c i.1 (S.z i.2)).both (S.u i.2).val
lemma up_p(S:Slide N x)(h: Even N.val)(i:Stag N):Bound Real.pi (angle S i):=orb _ _ h
lemma wage {x y:Bin}(p:peers x y)(z:Cover):mode (tmap x) z=mode (tmap y) z:=by obtain ⟨v,rfl⟩:=p; rw [map_stem,mode_phase,mode_periodic,mul_one]
lemma vind(X:Op (Single N))(Y:Stag N→Op SpinIdx)(h:X*(colU N).val=(colU N).val * arch Y): X=Dofu N Y:=by change X=twist _ (arch _); rw [twist_formula,← h,mul_assoc, (colU _).property.2,mul_one]
end YM.CF.Kea
