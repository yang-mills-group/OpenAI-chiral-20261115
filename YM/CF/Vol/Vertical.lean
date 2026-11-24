import YM.CF.Vol.Splat
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
abbrev OrnG(T:Tube G S)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(r:ℕ)(x:Ark T F):= RiftF r (Jazz T (choice s k) s x) (Jade T (choice s k) s x) T
abbrev OriG(T:Tube G S)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(r:ℕ)(x:Ark T F):= RiftI r (Jazz T (choice s k) s x) (Jade T (choice s k) s x) T (choice s k)
lemma nil_x (T:Tube G S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(s:Signed)(a:Fish (Key F G))(t:ℝ):
 let Z:=meal F x a; let y:Ark T F:= t • (0,a); Jazz T k s y=represent (t • Bid.pulled (Flat.labels Z) s) ∧ Jade T k s y=1:=by
 intro Z y; unfold Jazz Jade; rw [← Flat.facade_at (S:=S),←tray_x (F:=F) (x:=x)]; rw [show y.1=0 from smul_zero t,show y.2=t • a from rfl, trays_smul, show facadeX G (0:Mast G c)=1 from by simp [facadeX]]; exact ⟨rfl,(by funext i; simp [pull,Step.read])⟩
lemma vert_g(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(v:Fish (Key F G))(h:K.Funds S T) (Q:Marble n T (Jazz T (choice s k) s) (Jade T (choice s k) s) (choice s k) (Stores.till x) (0: Ark T F) C):
 let Z:=meal F x v; let p : Ark T F:=(0,v); (∀ i:Twin f,fderiv ℝ (fun y=> (OrnG T F k s (Stores.till x) y i)) 0 p= Rows.bump T x 1 k Z (s,.inl i)) ∧ (∀ i:Bond c, fderiv ℝ (fun y=> OriG T F k s (Stores.till x) y i) 0 p= Rows.bump T x 1 k Z (s,.inr i)):=by
 intro Z p; let χ(y:ℝ):Ark T F:= y • p; let g:= Jazz T (choice s k) s (F:=F); let P(y:ℝ):=g (χ y); let r:=Stores.till x; let a:=Bid.pulled (Flat.labels Z) s; have hp(t:ℝ):= nil_x T F x (choice s k) s v t; have hV:S.patch.Branches S.kernel G:=by rw [h.knobs]; exact h.kernel
 obtain ⟨X,D,hX,hD⟩:=h.feeds
 constructor
 · intro i
   apply (Push.side _ ((Q.roof i).analytic.differentiableAt (by simp)) p).unique; unfold RiftF; unfold p; simp_rw [(hp _).1,(hp _).2]
   refine HasDerivAt.sub_const (f:=fun y:ℝ=> T.Xf r (represent (y • a)) i) _ ?_
   unfold Xf plotted bump faceKick; simp only [Sum.elim_inl]; split
   · rw [Stack.finite_price _ _ _ _ hX]; simp_rw [← barrel_term,Stack.finite_price _ _ _ _ hX]; unfold r
     refine HasDerivAt.fun_sum (fun j _=> ?_) -- orientation
     rw [Flat.flat_curl]; have he := slot_deriv j i.1.1 a
     simp_rw [atSite_path] at he
     rw [fixed_facade,replica_one,show pull s 0 (1:Config G f)=1 from (by funext u; simp [pull, Step.read]),show travel (1:Config G f) i.1.1 j.walk=1 from by have hx:=stroll_zero (G:=G) j.walk (i.1.1); simpa using hx, G.adjoint_one]; exact he.const_smul (Stack.grouped T.up i.1.2 j)
   rw [Flat.flat_curl]; exact (curvature_of_hasDerivAt (face_deriv i.1 a)).const_smul (Real.sqrt T.high.direct)
 intro i
 apply (Push.side _ ((Q.jamb i).analytic.differentiableAt (by simp)) p).unique; unfold RiftI Rows.bump noiseKick; unfold p; simp_rw [Sum.elim_inr,(hp _).1,(hp _).2]; rw [Flat.flat_probe _ _ _ _ hV]
 unfold Tube.Z; simp_rw [Pi.one_apply,one_mul,G.curvature_inv,smul_neg] -- tune neg
 have hv:= curvature_of_hasDerivAt (Push.prices S hV i (choice s k) a)
 apply HasDerivAt.sub_const; exact ((hv.const_smul (Real.sqrt S.kernel.penalty)).neg)
end YM.CF.Vol
