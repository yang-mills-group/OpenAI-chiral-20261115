import YM.CF.Laic.Pell
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {n c:Side}{E: Type}[NormedAddCommGroup E][NormedSpace ℝ E]{Z:E→Bkg n}{k:ℕ}{a:ℝ}
-- line analytic growth
section fro
open scoped Matrix.Norms.Frobenius
lemma ventAllow (a:ℝ)(h:0≤a)(k:ℕ)(d:ℝ)(p:0<d):∃ C:ℝ,0≤C ∧ ∀ R:ℕ, travelCost SU.group k (8*(R+1)) a ≤ C*Real.exp (d* R):=by
 let M:ℝ:= 2^k; have hk:0<M:=by positivity
 let u:ℝ:= 1+9*M; have hu:0<u:=by unfold u; positivity
 let A:=‖(1:group.Mat)‖; let b:= Real.exp 1*A; let f:=composeCost k (b*u^k) a; have hb:0≤b:=mul_nonneg (by positivity) (norm_nonneg _); have hf:0≤f:=by unfold f composeCost; positivity
 let v:= Iteration.momentPrice k d
 refine ⟨f*v,mul_nonneg hf (Iteration.momentPrice_pos _ p|>.le),fun R=>?_⟩; let r:ℝ:=R; have he:0≤r:=Nat.cast_nonneg _; apply le_trans _ (mul_le_mul_of_nonneg_left (Iteration.spendMoment k p he) hf |>.trans_eq (by ring)); unfold travelCost; let T:=a
 have hh: (((1+(2:ℝ)^k*(1+ ↑(8*(R+1):ℕ))):ℝ)) ≤ u*(1+r):=by
    push_cast; unfold u r M; ring_nf; have hp:0 ≤ (2:ℝ)^k*R:=by positivity
    unfold r at he; linarith
 calc
   _ ≤ composeCost k (b*(u*(1+r))^k) a:=by unfold composeCost b; change (k.factorial:ℝ) * ((Real.exp 1*A)*_)*(1+a)^k ≤ (k.factorial:ℝ) *((Real.exp 1*A)*_) *(1+a)^k; gcongr -- tune
   _ = _:=by unfold f composeCost; rw [mul_pow]; ring
private def plaw : group.Mat→L[ℝ] group.Color:=group.projectColor.toContinuousLinearMap ∘L ((1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - (starL' ℝ (A:=group.Mat)).toContinuousLinearMap))
lemma psalm (k:ℕ)(h:0≤a)(d:ℝ)(p:0<d):∃ C:ℝ,0<C∧∀ {n:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{Z:E→ Bkg n}, EnvM k Z 0 a→∀ (t:Wind n)(x: Site n)(v:ℕ),dial x t ≤ v → Allows k (fun y=> silt x t (Z y)) 0 (C*Real.exp (d*v)):=by
 obtain ⟨C,hc,H⟩:= ventAllow a h k d p; let R:= normL (A:=group.Mat) plaw; have hx:0≤R:=normZ (A:=group.Mat) _
 refine ⟨1+R*C,by positivity,?_⟩; intro n E _ _ Z hZ t x v hv; have he := (travel_jets hZ.ink x (w:=boot x t) (le_trans (leanB ..) (by omega:8*_ ≤ 8*(v+1)))).mono (H v)
 have hw := he.linear plaw le_rfl; refine ((hw.germ (Eventually.of_forall fun y=>?_)).mono ?_); · unfold silt Gauge.curvature; rw [group.mat_inv]; rfl -- tune
 exact le_trans (le_of_eq (mul_assoc R C _).symm) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
lemma bunt (f:E→SU.E)(h: Allows k (fun i=>group.mat (f i)) 0 a)(i j: Fin group.repDim):Allows k (fun x=> fund (f x) i j) 0 (dGray a):=((h.linear (entry_F i j) le_rfl).mono (pike h.nonneg _ _))
lemma pf_b (k:ℕ)(d:ℝ)(p:0<d)(t:0≤a): ∃ C:ℝ,0≤C∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}{Z:E→Bkg n}, EnvM k Z 0 a→∀ (i j:Site n)(w:ℕ),separation i j≤ w→∀ u v:Fin group.repDim, Allows k (fun x=>fund (travel (Z x) i (shiftH i j)) u v) 0 (C*Real.exp (d*w)):=by
 obtain ⟨C,hc,H⟩:=ventAllow a t k d p; refine ⟨dGray C,dGray_pos hc,?_⟩; intro E _ _ n Z h i j w he u v
 have hw : (shiftH i j).length≤8*(w+1):=by have ht:=short i j; omega
 have hp:=bunt _ ((travel_jets h.ink i hw).mono (H w)) u v; exact hp.mono (by unfold dGray; rw [mul_assoc])
lemma swellT {F:E→Bkg (More n)}(p:EnvM k F 0 a)(i:Signed): EnvM k (Yg (incX i) ∘ F) 0 a:=by
 refine ⟨fun e=>?_⟩; simp_rw [Function.comp_apply,Ywin]; unfold Lattice.pull Step.read; split
 · exact (p.ink _).inverse (f:=fun x=>F x _)
 exact p.ink _
end fro
end YM.CF.Laic
