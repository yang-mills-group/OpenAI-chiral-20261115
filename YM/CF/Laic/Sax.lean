import YM.CF.Laic.Stubs
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N c:Side}{T:RG.StepData (More n) (More N)}{F: Forest T.ratio}{X:Cloud n→Op (Single n)}{a b:ℝ}
abbrev Coat(n:Side):=Primary (More n) group
def colorL: group.Color ≃L[ℝ] (group.ColorIndex→ℝ) :=(show group.Color≃ₗ[ℝ] _ from { toFun:=WithLp.ofLp,invFun:=WithLp.toLp 2,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }).toContinuousLinearEquiv -- tune
private lemma fees (v:Edge (Site (More n)))(x:group.Color): put group (More n) v x=∑ i:group.ColorIndex,x i • whisp (n:=n) (Push.Uniform.bolt (Trot (More n) v,i)):=by
 funext a; rw [Finset.sum_apply]; apply PiLp.ext; intro j; rw [WithLp.ofLp_sum, Finset.sum_apply]; change (Pi.single (M:=fun _=> group.Color) (Trot _ v) x a).ofLp j=∑ i:group.ColorIndex, x i * Push.Uniform.bolt (Trot _ v,i) (a,j)
 by_cases h:a=Trot _ v <;>simp [Pi.single_apply,h,Push.Uniform.bolt]; -- tune
variable {k:ℕ}
private def fareC(k:ℕ):ℝ:=Fintype.card (Fin k→ group.ColorIndex) * ((k.factorial:ℝ)⁻¹ * ‖colorL.toContinuousLinearMap‖^k)
lemma fare_pos(k:ℕ):0≤fareC k:=by unfold fareC; positivity
lemma feeJet (p:ContDiffAt ℝ ω X 0)(x:Site (More n))(v:Fin k→Blip (More n))(i j:Single n)(h:Beacon (aTrait T) a k (fun y=> X (whisp y) i j) (T.ratio.embed x) 0 b)(hx:0≤b)(t:0<a):
 ‖timeA ((boc i j).compContinuousMultilinearMap (cake k X)) v‖ ≤ fareC k * b*Real.exp (-a*∑ l:Fin k, (separation x (v l).1:ℝ)):=by
 set Δ :ℝ:=∑ l:Fin k,(separation x (v l).1 :ℝ); let H:= (boc i j).compContinuousMultilinearMap (cake k X); let L:=(tint group (Body 1 (More n))); let f :=(boc i j)∘ X; have hg:ContDiffAt ℝ ω f (L 0):=by rw [map_zero]; exact (boc i j).contDiff.contDiffAt.comp _ p
 let s := Real.exp (-a*Δ); let u:ℝ:=(k.factorial:ℝ)⁻¹; let C:= colorL.toContinuousLinearMap
 apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (mul_nonneg (fare_pos _) hx) (by positivity)); intro r
 let V (d:Fin k→group.ColorIndex)(i:Fin k) : Coat n:= (Trot _ (v i),d i)
 have hp(d:Fin k→group.ColorIndex): H (fun i=> L (Push.Uniform.bolt (V d i)))=u • entry (f∘ L) 0 (V d) :=by
    unfold Push.Uniform.entry; rw [show iteratedFDeriv _ k (f ∘ L) 0 =_ from iter_lin_at (L:=L.toContinuousLinearMap) (k:=k) (hg.of_le le_top),map_zero,(boc i j).iteratedFDeriv_comp_left p le_top,ContinuousMultilinearMap.compContinuousLinearMap_apply]; change boc i j (u • _) = u • boc i j _; rw [map_smul]; rfl
 have hz(g:Fin k→group.ColorIndex):spanSites (aTrait T) (T.ratio.embed x) (V g)= T.ratio.count.val * ∑ i, separation x (v i).1:=by
    unfold spanSites V; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; exact emptio ..
 have hv(d: Fin k → group.ColorIndex):‖entry (f ∘ L) 0 (V d)‖≤ b *s:=by
    refine le_trans (h k le_rfl (V d)) ?_; unfold s; rw [hz]; apply mul_le_mul_of_nonneg_left _ hx; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (by linarith); unfold Δ; rw [←Nat.cast_sum]; exact_mod_cast Nat.le_mul_of_pos_left _ T.ratio.count.property
 let t(i):=r i
 have hh(d:Fin k→group.ColorIndex): ‖∏ i, r i (d i)‖≤‖C‖^k*(∏ i,‖r i‖):=by
    rw [norm_prod]; calc
      _ ≤ ∏ i:Fin k,(‖C‖* ‖r i‖):=Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> (norm_le_pi_norm (C (r i)) (d i)).trans (C.le_opNorm _))
      _ = _:=by rw [Finset.prod_mul_distrib, Finset.prod_const,card_univ,Fintype.card_fin]
 change ‖H (fun i=> put group (More n) (v i) (r i))‖≤ _; simp_rw [fees]; rw [ContinuousMultilinearMap.map_sum]
 let M:=‖C‖^k*(∏ i,‖r i‖)*(u*(b*s))
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>M) ?_).trans_eq ?_); intro g _; rw [ContinuousMultilinearMap.map_smul_univ]; change ‖(∏ i,r i (g i)) • H (fun k=> L (Push.Uniform.bolt (V g k)))‖≤ M; rw [hp g,norm_smul]; let R:= u • entry (f∘ L) 0 (V g); refine mul_le_mul (hh g) ?_ (norm_nonneg _) (by positivity); rw [norm_smul, Real.norm_of_nonneg (show 0≤u by unfold u; positivity)]; apply mul_le_mul_of_nonneg_left (hv g); positivity
 simp only [Finset.sum_const,card_univ,nsmul_eq_mul]; unfold M u fareC C s; ring
def dime (k:ℕ) (a b:ℝ):= let h:= countCost (a/2); (fareC k * (2*b))*((Fintype.card Axis:ℝ)*h)^k * ((↑(Fintype.card (SpinIdx×Slot)):ℝ)*h)
lemma stipulated (g:HoldX (aTrait T) (popH T) (X∘ whisp) a b k)(t:0<a): ContDiffAt ℝ ω X 0∧∀ i, entice (a/2) (cake k X) i≤ dime k a b:=by
 let L:=(tint group (Body 1 (More n))); have he:X=(X ∘ whisp) ∘ L.symm:=by funext y; change _=X (L (L.symm y)); rw [ContinuousLinearEquiv.apply_symm_apply];
 have hp: ContDiffAt ℝ ω X 0:=by
    let f:=X∘whisp; have hx: ContDiffAt ℝ ω f (L.symm 0):=by rw [map_zero]; exact g.glow
    nth_rw 1 [he]; exact hx.comp 0 L.symm.contDiff.contDiffAt
 refine ⟨hp,fun i=>?_⟩; let h:= a/2; let u:= countCost h; let v:= fareC k*(2*b); have hs:0<h:= half_pos t; have hb:=g.funds; have hc:0<u:= count_pos hs; let x:=place_x i
 let y(e:Blip (More n)):= Decay h x e.1
 have hz:0≤v:=mul_nonneg (fare_pos k) (by positivity)
 have hA: ∑ i:Blip (More n),y i ≤ Fintype.card Axis*u:=by unfold Blip Edge; rw [Fintype.sum_prod_type]; change ∑ i:Site (More n),∑ _:Axis,Decay h x i ≤_; simp_rw [Finset.sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left (decay_count hs x) (by positivity)
 let A := v*((Fintype.card Axis:ℝ)*u)^k; have hC(j:Single n): tiltV x ((boc i j).compContinuousMultilinearMap (cake k X)) h (gear i j) ≤ A*Decay h x (place_x j):=by
   let Y:= place_x j; let B:=Decay a (popH T i) (popH T j)
   have h'(r: Fin k→ Blip (More n)):let F:= Real.exp (h*(gear i j+∑ i, (separation x (r i).1:ℝ))); F*‖timeA ((boc i j).compContinuousMultilinearMap (cake k X)) r‖ ≤ v* Decay h x Y* ∏ i, y (r i):=by
      intro F; have hx: Beacon _ a k (fun y=>X (whisp y) i j) (T.ratio.embed x) 0 ((2*b)* B):= pendant (Nacre.tort.mp g.glow) g.law i j; apply (mul_le_mul_of_nonneg_left (feeJet hp x r i j hx (mul_nonneg (by positivity) (decay_pos ..|>.le)) t) (Real.exp_pos _|>.le)).trans; let z:ℝ:= ∑ i:Fin k,(separation x (r i).1:ℝ)
      have hw : B ≤ Decay a x Y:=by unfold B Decay popH; rw [Function.comp_apply,Function.comp_apply,emptio]; apply Real.exp_monotone; unfold x Y; apply mul_le_mul_of_nonpos_left _ (by linarith); exact_mod_cast Nat.le_mul_of_pos_left _ T.ratio.count.property
      have hh:F*(Decay a x Y)*Real.exp (-a*z) = Decay h x Y*∏ i, y (r i):=by simp only [F,y,Decay]; rw [←Real.exp_sum]; simp_rw [←Finset.mul_sum,←Real.exp_add]; congr 1; unfold z x Y gear h; ring
      change F*(fareC k*(2*b*B)*Real.exp (-a*z))≤ _; rw [mul_assoc v,←hh]; unfold v; calc
        _ = (fareC k*(2*b)) * (F*B*Real.exp (-a*z)):=by ring
        _ ≤ _:=by gcongr
   unfold tiltV; apply (sum_le_sum (fun r (_:r∈(univ:Finset _))=> h' r)).trans; rw [← Finset.mul_sum]; unfold y; rw [show ∑ v: Fin k→ Blip (More n),∏ i:Fin k,Decay h x (v i).1= (∑ i: Blip (More n),y i)^k from ?_]; unfold A; rw [mul_right_comm v]; gcongr; exact (decay_pos ..).le; exact Finset.sum_nonneg fun i _=>(decay_pos ..).le; -- leaves hA
   convert (Finset.prod_univ_sum (fun i:Fin k=> (Finset.univ:Finset (Blip (More n)))) (fun _ i=> y i)).symm using 1 <;> first|rfl|simp
 apply (sum_le_sum (fun i (_:i∈(univ: Finset _))=>hC i)).trans; rw [←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left (Multiplicity.count _ (ringM id Function.injective_id) hs x) (show 0≤ A from by positivity)
end YM.CF.Laic
