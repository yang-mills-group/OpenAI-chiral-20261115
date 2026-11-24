import YM.CF.Vol.Slush
import YM.CF.Vol.Pallas
import YM.CF.Slate.Luce
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
lemma annual (K:Teller G)(P:Patch)(p:G.Simple) (hP:P.Branches K.bind G)(n l:ℕ)(hp:3 ≤ n)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)) :∃ C ε D:ℝ,0< C ∧0<ε ∧0<D∧∀ᶠ x in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F →∀ (k:S.Choices)(i:Slots S), stance (arcX T x F k l i) (D*temp x^(l+1)) ∧∀ u:Mast G c, ‖u‖ < ε → Allows n (arcX T x F k l i) u C:=by
 obtain ⟨A,v,b,hA,hv,hb,H⟩:= lift_paid p K P hP n l (by omega) W; obtain ⟨D,C,e,hd,hC,he,Q⟩:= commercial K p P hP l n hp W; obtain ⟨M,r,hM,hr,Y⟩:= drawn K P (n+2) (by omega) W hP
 let M':=max 1 A; have ht:0<M':=zero_lt_one.trans_le (le_max_left ..); let ε:=min (min r 1) (min b (e/M')); let C' := Jet.composeCost n M 1+ Jet.composeCost n C M'
 refine ⟨C',ε,D,by unfold C' Jet.composeCost; positivity, lt_min (lt_min hr zero_lt_one) (lt_min hb (div_pos he ht)),hd,?_⟩; filter_upwards [H,Q,eventually_gt_atTop (0:ℝ)] with x hx hq hv c f S T F h g k i
 let s:=i.1; let f:=skyB T x F k i; let g':= gloss T x F k i; let m:=sol S T k x F l; obtain ⟨z,hz,hs,H⟩:= hx S T F h g
 have hcX(t)(p:‖t‖<r):Allows n f t M:=by obtain ⟨hh,H'⟩:= Y _ _ F h.funds.1 h.got s (choice s k) (Stores.till x); cases i with| mk s i=>cases i; exact ((paper ((H' _ p).roof _)).order (by omega)); exact ((paper ((H' _ p).jamb _)).order (by omega)) -- tune
 have hAX:=hq S T F h g k s; obtain ⟨hm,hf,ho⟩:=H k 0 (by simpa using hb)
 let L:Mast G c→L[ℝ] Ark T F:= ContinuousLinearMap.inl ℝ _ _; let U(t:Mast G c): Ark T F:= (t,m t); have hu : f ∘ L + (g' ∘ U)=arcX T x F k l i:=by ext1 t; rw [Pi.add_apply,arcX,drop_x]; rfl
 have hg(y)(hx:‖y‖< b):Allows n m y A:= (H k y hx).1
 have ht(y)(hx:‖y‖<e):Allows n g' y C:=(hAX.ears y hx).Y i
 let R:= D*temp x^(l+1); have hR:0≤ R:=mul_nonneg hd.le (pow_nonneg (temp_nonneg _) _)
 rw [← hu]; refine ⟨?_,fun u hd=> ?_⟩
 · have ht:=((ht 0 (by simpa)).order (show 1 ≤ n by omega)).smooth.differentiableAt (by norm_cast)
   refine arc_move (G:=G) m f g' (((hcX _ (by simpa)).order (show 1 ≤ n by omega)).smooth.differentiableAt (by norm_cast)) ht ((hm.order (show 1 ≤ n by omega)).smooth.differentiableAt (by norm_cast)) hf ?_ ?_ ?_ hR
   · intro v; unfold g' gloss dragB; change Rows.bump T _ _ k (meal F x 0) i=_; rw [map_zero,van_g h.funds.1]; rfl
   · intro y
     obtain ⟨q,p⟩:= (vert_g T x F k s y h.funds.1 ((Y _ _ F h.funds.1 h.got s (choice s k) (Stores.till x)).2 _ (by simpa)))
     have hx:= (down_D T x F k i h.funds.1 ht (0,y)).2
     rcases i with ⟨s,i⟩; cases i; exact (q _).trans hx.symm; exact (p _).trans hx.symm
   rcases i with ⟨s,i⟩; cases i; exact hAX.funds.roof _; exact hAX.funds.jamb _
 have hA':‖u‖<b:=hd.trans_le ((min_le_right ..).trans (min_le_left ..)); have ht':‖u‖<1:=hd.trans_le ((min_le_left ..).trans (min_le_right ..))
 have hL(i:Mast G c):‖L i‖≤ ‖i‖:= by change max _ _ ≤ ‖i‖; exact max_le le_rfl (by rw [show (L i).2=(0:Fish _) from rfl]; simp)
 have hX:‖U u‖< e:=by
    have hv:=miles (x:=u) (show 1 ≤ n by omega) hg hb hA'; rw [show m 0=0 from hf,sub_zero] at hv -- tune namespace?
    refine lt_of_le_of_lt (max_le (le_mul_of_one_le_left (norm_nonneg u) (le_max_left ..)) (hv.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)))) (((mul_comm ..).trans_lt ((lt_div_iff₀ (show 0<M' by unfold M'; positivity)).mp (hd.trans_le ((min_le_right ..).trans (min_le_right ..)))))) -- positivity
 have hU:Allows n U u M':= ((Jet.allows_linear (L:=ContinuousLinearMap.id ℝ (Mast G c)) (ContinuousLinearMap.norm_id_le ..) ht'.le).mono (le_max_left ..)).pair ((hg u hA').mono (le_max_right ..))
 exact ((hcX _ ((hL u).trans_lt (hd.trans_le ((min_le_left ..).trans (min_le_left ..))))).comp (Jet.allows_linear (L:=L) (L.opNorm_le_bound zero_le_one fun i=> (hL i).trans_eq (one_mul _).symm) ((hL u).trans ht'.le))).add ((ht _ hX).comp hU)
-- add to Vol.Fresh pieces; exact
abbrev OreK (T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(i:Slots S)(u:Ark T F):ℝ:= -inner ℝ (arcX T x F k l i u.1) (gloss T x F k i u)
lemma gambit(K:Teller G)(P:Patch)(p:G.Simple) (hP:P.Branches K.bind G)(n l:ℕ)(hp:3 ≤ n)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)) : ∃ ε C D:ℝ,0< ε∧0<C∧0<D∧∀ᶠ x in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x →sizedP G P K S T F →∀ (k:S.Choices)(i:Slots S), KnotP (OreK T x F k l i) n (D* temp x^(l+1)) C ε :=by
 obtain ⟨C,u,D,hC,hu,hd,H⟩:= annual K P p hP n l hp W; obtain ⟨Y,X,b,hy,hX,hb,Q⟩:=commercial K p P hP l n hp W
 let t:= min (min u b) 1; let A:=Jet.composeCost n C 1; have ht:0<t:=lt_min (lt_min hu hb) zero_lt_one
 refine ⟨t,2^n*A*X,2*D*X,ht,by unfold A Jet.composeCost; positivity,by positivity,?_⟩; filter_upwards [H,Q] with x h p c f S T F v r k i
 let L: Ark T F→L[ℝ] Mast G c:= ContinuousLinearMap.fst ℝ _ _; let f:= arcX T x F k l i; let z:= D*temp x^(l+1); let g:= gloss T x F k i; have hx:=p S T F v r k i.1
 have hL: ‖L‖ ≤1:= ContinuousLinearMap.norm_fst_le ..; obtain ⟨h,H⟩:= h S T F v r k i
 have hp: 2 ≤ n:=by omega
 have he:stance (f ∘ L) z:=by
    have hs: ContDiffAt ℝ (↑(1:ℕ)) f (L 0):=((show ‖L 0‖<u by simpa only [map_zero,norm_zero] using hu)|> H (L 0)|>.order (show 1 ≤ n by omega)).smooth -- tune
    refine ⟨by rw [Function.comp_apply,map_zero]; exact h.origin,?_⟩; rw [fderiv_comp _ (hs.differentiableAt (by norm_cast)) L.differentiableAt,map_zero,L.fderiv]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hL).trans h.rud)
 have hu:= Yacht (g':=g) (t:=z) (fun x (p:‖x‖< t)=> (H (L x) ((norm_fst_le x).trans_lt (p.trans_le ((min_le_left ..).trans (min_le_left ..))))).comp (f:=L) (Jet.allows_linear hL ((norm_fst_le x).trans (p.le.trans (min_le_right ..))))) (fun x p=> (hx.ears x (p.trans_le ((min_le_left ..).trans (min_le_right ..)))).Y i) he (hx.J i) ht hp
 have hq:= hu.scale (-1) ht hp; simp only [neg_one_smul,abs_neg,abs_one,one_mul] at hq; exact hq.mono (le_of_eq (by unfold z; ring)) le_rfl le_rfl
end YM.CF.Slate
