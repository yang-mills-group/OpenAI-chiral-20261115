import YM.CF.Nacre.Shelf
import YM.CF.Nacre.Bliss
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{m:ℕ}
def ActZ(g:Site (More n)→E)(X:Op (Single n)) := twist (tradew n g) X
abbrev Rhyme(n:Side):= Cloud n→ Op (Single n)
structure Motion (X:Rhyme n):Prop where
 gauge (g:E)(x:Cloud n):∀ᶠ t:ℝ in 𝓝 0,X (t • MarkT g x)=ActZ (fun _=> g) (X (t • x))
 slope(t:Cover)(x:Cloud n):∀ᶠ s:ℝ in 𝓝 0,X (s • SubMotion t x)=ZoneH (lagX t) (X (s • x))
 plane(a:Signed)(x:Cloud n):∀ᶠ s:ℝ in 𝓝 0,X (s • litX a x)=ZoneH (incX a) (X (s • x))
 current(x:Cloud n)(z:Site (More n)):∀ᶠ s:ℝ in 𝓝 0,X (race z x s)=ActZ (ramps z x s) (X (s • x))
namespace Motion
variable {X:Rhyme n}(H:Motion X)(p:ContDiffAt ℝ (m:ℕ) X 0)(h:cFoot m X)
include H p h
lemma est: RaysX (trim m X):=by
 have he:= (argent p).mp h; let f:=trim m X; constructor
 · intro g x; apply tendsto_nhds_unique (he (MarkT g x)); let V:=(twist (folk g n)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
   apply (((V.continuous.tendsto _).comp (he x))).congr'
   filter_upwards [(H.gauge g x).filter_mono nhdsWithin_le_nhds] with t ht; change V ((t^m)⁻¹ • _) = _; rw [map_smul,ht]; rfl
 intro t x; apply tendsto_nhds_unique (he (SubMotion t x)); refine (((ZoneH (lagX t)).continuous.tendsto _).comp (he x)).congr' ?_
 filter_upwards [(H.slope t x).filter_mono nhdsWithin_le_nhds] with v hv; change ZoneH (lagX t) ((v^m)⁻¹ • _)= _; rw [map_smul,hv]
lemma frost(x:Cloud n)(z:Site (More n)):trim m X (fullG z x)=trim m X x:=by
 let V:=trim m X; let F:=𝓝[≠] (0:ℝ); let G(t:ℝ):=ramps z x t; let L(t:ℝ):=(tradew n (G t)); have hl:Continuous fun t=>(L t).val:=by
   apply continuous_matrix; rintro ⟨u,i⟩ ⟨v,j⟩; change Continuous fun t:ℝ=> jump (Equiv.refl (HopK n)) (fun x=>(matter (G t (terse x))).val) (u,i) (v,j); simp only [jump_apply]; split; · exact (matter_cont.comp (group.lieExp_cont.comp (f:=fun t:ℝ=> t • (sap z (collect group x) (terse u))) (by fun_prop))).matrix_elem i j
   exact continuous_const
 let A(p:ℝ× Op (Single n)):= ActZ (G p.1) p.2
 have he:Continuous A:= ((hl.comp continuous_fst).mul (continuous_snd (X:=ℝ) (Y:=Op (Single n)))).mul (hl.comp continuous_fst).star -- twist_formula defeq
 have hu:=he.tendsto (0,V x); have hx:= hu.comp (tendsto_id.mono_left nhdsWithin_le_nhds |>.prodMk_nhds ((argent p).mp h x))
 have hA:A (0,V x)=V x:=by
    change twist (L 0) _= _; have hp:(L 0).val=1:=by unfold L G; rw [ramps_0]; unfold tradew; simp only [Pi.one_apply,map_one]; exact jump_id
    rw [twist_formula,hp,one_mul,star_one,mul_one]
 apply tendsto_nhds_unique (flares (race z x) p ((sport z x).of_le le_top) _ (roundS ..) (tough ..) h); rw [hA] at hx; apply hx.congr'
 filter_upwards [(H.current x z).filter_mono nhdsWithin_le_nhds] with t ht; change twist _ ((t^m)⁻¹ • _) = _; rw [map_smul,ht]; rfl
lemma hail(a:Signed)(x:Cloud n): trim m X (litX a x)=ZoneH (incX a) (trim m X x):=by
 have he:=(argent p).mp h; apply tendsto_nhds_unique (he (litX a x)); refine (((ZoneH (incX a)).continuous.tendsto _).comp (he x)).congr' ?_
 filter_upwards [(H.plane a x).filter_mono nhdsWithin_le_nhds] with t ht; change ZoneH (incX a) ((t^m)⁻¹ • _)= _; rw [map_smul,ht]
end Motion

def boc(x y:Single n): Op (Single n)→L[ℝ]ℂ:= (show Op (Single n)→ₗ[ℝ]ℂ from ⟨⟨fun p=>p x y,fun a b=>rfl⟩,fun a b=>rfl⟩).toContinuousLinearMap
def entice(a:ℝ)(W:AimX m SU.group (More n) (Op (Single n)))(i: Single n):ℝ:=∑ j,tiltV (place_x i) ((boc i j).compContinuousMultilinearMap W) a (gear i j)
theorem posed (m:ℕ)(a:ℝ)(h:0<a): ∃ b D:ℝ,0<b ∧ 0<D∧∀ (n:Side)(X:Rhyme n), ContDiffAt ℝ (m:ℕ) X 0→ Motion X→ cFoot m X→ ∀ C:ℝ,(∀ i,entice a (cake m X) i ≤C)→∃ K:Toy m n,Prints K∧ handy K∧ spurTx K=trim m X ∧∀ i,balance b K i ≤ C*D:=by
 obtain ⟨b,K,hb,hK,H⟩:= ration a h m; refine ⟨b,K*sugarK,hb,mul_pos hK (by unfold sugarK; positivity),fun n X p u w C e=>?_⟩
 let W(i j):=(boc i j).compContinuousMultilinearMap (cake m X)
 choose P f H using fun i j:Single n=>H (place_x i) (W i j) (gear i j) (Nat.cast_nonneg _); let V:=trim m X
 have ht: pyre P=V:=by funext x; ext i j; have he:= H i j x; change _=V x i j; change Tensor.diagonal (cake m X) (fullG (place_x i) x) i j=_ at he; rw [show V x= _ from (u.frost p w x (place_x i)).symm]; exact he.symm
 obtain ⟨T,v',v,hp,U⟩:= lit P (show RaysX (pyre P) from ht.symm ▸ u.est p w)
 have hx:pyre T=V:=hp.symm.trans ht
 refine ⟨T,v,v',?_,fun i=>?_⟩
 · funext x; have he (i:Signed):ZoneH (incX i) (pyre T (litX i⁻¹ x))=V x:=by rw [hx]; unfold V; rw [u.hail p w,zno,wink,inv_mul_cancel,bareI] -- tune
   unfold spurTx; simp_rw [he]; change _= V x; rw [sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
 have hv(j: Single n): balance b P j≤ K*C:=by apply le_trans _ (mul_le_mul_of_nonneg_left (e j) hK.le); unfold entice; rw [mul_sum]; exact sum_le_sum fun i _=> f _ _
 exact (U _ _ hv i).trans_eq (by ring)
end YM.CF.Nacre
