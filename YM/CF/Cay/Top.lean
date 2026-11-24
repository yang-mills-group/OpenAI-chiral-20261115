import YM.CF.Cay.Apt
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open Matrix Far AnalyticBridge.RelativeLogdet
section
abbrev coastA (j l:ℕ):=coverB l j+2
abbrev coarseZ(P:Patch)(r n l:ℕ)(s x β C D M v:ℝ):= let X:= bankU*v; let L:=composeCost n ((M+M)*s^3) 1; |coupling β|⁻¹ * (X*(C*(aimC x* D^2)))+ X*(2^n*(C*lamp x)*v)+ |β| * (about P.L (horn x l)*composeCost r (2^r*composeCost r ((M+M)*s^3) 1+2^r*(2^r*composeCost r ((M+M)*s^3) 1)) (1/2)) -- correct uses r?? rebate n! r=n
abbrev glenZ(n l:ℕ)(β M v s:ℝ):= composeCost n (β*coupling β *(bankU*v*(2^n*M*(M*s^(l+2))))+(bankU*v)*(v*(M*s^3))) (1/2)
structure Carbon (P:Patch)(x β d w v a b D A C C' M:ℝ)(n l j:ℕ)(T:Tube G S)(Z:ζ)(q:Chi):Prop where
-- s:= burn
 par(i: Signed)(t:Along S): t ∈ rush x Z.key i j →
    let X:= dense T x q d l β i t; let y':= burn a x P; let Q:= mon3 n 3 A (M*y') M β v y'; let Q':=mon3 n 4 A (M*y') M β v y'; let S0(u):=shotB X (Z.atop u x); let S1(u):=shotB X (violet (Z.atop u x));
    Allows n S0 0 Q ∧ Allows n S1 0 Q∧ Allows n (S0+ S1) 0 (Q'+Q')
 cost(e:Bond f):Allows n (fun i=> opus T x q d l β j e (Z.atop i x)) 0 (coarseZ P n n l (burn a x P) x β C (fiery G x P.L) M v)
 star(e:Bond f)(h:S.ratio.parent e.1∉ Z.key.dome (coastA j l * radiusB x)): Allows n (fun i=> opus T x q d l β j e (Z.atop i x)) 0 (glenZ (n+4) l β C' v (burn b x P))
-- w D unused clean
lemma post (P:Patch)(K:Teller G)(n l j:ℕ) (W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+4+2))(V:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+4+3))(W':Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1))(p:P.Branches K.bind G)(hg:2  ≤  n)(hv:l ≤ 18)(hx:l+78 ≤ j)(D d:ℝ)(ht:0 ≤  D)(hd:0<d)(q:Chi):∃ a b A C C' M:ℝ,0<a∧0<b∧0<C∧0<C'∧0<A∧0<M∧∀ᶠ x in atTop,∀ β∈ Set.Icc (y G P.L x/2) (2*y G P.L x), let u:=D* Scales.p G P.L x; let d':=d*fiery G x P.L; ∀{c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x→ ∀ (Z:Monk G S)(L:ℝ),0  ≤  L→ ‖Z.z‖  ≤  L→ L ≤  u → (coverB l j+coverB l j+101)*radiusB x ≤  c.val → sizedP G P K S T Z.park→ Z.key.flags=RG.flags (temp x) Z.V→ Carbon P x β d' d L a b D A C C' M n l j T Z q:=by
 obtain ⟨a,A,v,w,E,M,H,ha,hA,hw,hH,hM,h⟩:=sting K P p (n+4) l (j-2) (by omega) hv V W D ht; obtain ⟨b,A',v',w',E',M',F,hb,hA',hw',hF,hM',h'⟩:= sting K P p (n+4) l (coverB l j) (by omega) hv V W D ht; obtain ⟨C,hC,hK⟩:=turnsX n l d hd K P p (by omega) hv W' q -- need hn!
 refine ⟨a,b,A,C,A',M,ha,hb,hC,hA',hA,hM,?_⟩; filter_upwards [h,h',hK] with x H1 H2 H3; obtain ⟨h1,h2,h3,h4,h5,h6⟩:=H1; obtain ⟨k1,k2,k3,k4,k5,k6⟩:=H2; intro β hβ u d' c f S T Hx Z L hl hL hbX Y Hk Kx
 let Q:=MossX n l x Z.key Z.park T Z.V Z.k C d' (fiery G x P.L) q; have hQ:Q:= by unfold Q d'; rw [← Hx.got]; exact H3 S T Hx Z.key Z.park Z.V Hk Kx Z.k
 obtain ⟨hp,hz⟩:= h6 _ hβ; obtain ⟨-,hn⟩:= k6 _ hβ; let s:= burn a x P
 have hf(i:Signed)(t:Along S)(hp:t∈rush x Z.key i j):=hz S T Hx Z (herald S i t) q (Nat.le_trans (Nat.mul_le_mul_right _ (by unfold coverB; omega)) Y) Hk Kx (show herald S i t∉Z.key.dome _ from (by rw [Nat.sub_add_cancel (show 2  ≤  j by omega)]; exact (mem_filter.mp hp).2)) (hL.trans hbX)
 have hbL:u= D*Scales.p G P.L x:=rfl; let G'(s):=composeCost n ((M+M)*s^3) 1 -- likely invalid Nat
 have heL: |coupling β| * (L*A)  ≤  |coupling β| *(D*Scales.p G P.L x * A):=by apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbX hA.le) (abs_nonneg _)
 constructor
 · intro i t H X y' Q Q' S0 S1; obtain ⟨v,V,Hh,Vh,U,g,R,H⟩:= hf i t H; exact peer_p L hL Hx.funds.1 hw h5 h3 h4 le_rfl (p:=herald S i t) (by rw [separation_self,zero_add]; unfold horn; exact Nat.mul_le_mul_right _ (by omega)) H v V Hh (heL.trans Vh) (U _ _)
 · intro e; let U:= 2^n * G' s; let K:=composeCost n (U+2^n*U) (1/2); have hσ:0  ≤  s:=h3.le; have hk:0  ≤  K:=by unfold K U G' Jet.composeCost; positivity
   apply (speaks e j (C:=K) ?_ (terra e L hL hQ) hQ.ready h5 hk).mono (Eq.le ?_); swap
   · unfold coarseZ K U G' s; rw [Hx.got]; ring
   intro i j v; obtain ⟨v',k,Hh,Vh,U,g,R,H⟩:= hf i j v; exact rebate L hL Hx.funds.1 hw h5 h3 h4 h2 le_rfl (by rw [separation_self,zero_add]; unfold horn; exact Nat.mul_le_mul_right _ (by omega)) H v' k Hh (heL.trans Vh) (U _ _) e -- shadow U
 intro e hp'; obtain ⟨v,hq,Hh,Vh,U,g,R,H⟩:= hn S T Hx Z (S.ratio.parent e.1) q Y Hk Kx hp' (hL.trans hbX)
 exact (plot_p (d:=d') (q:=q) (m:=coverB l j+1) e v' E' Hx.funds.1 hp hw' (by omega) k3 k4 v k5 H (by omega) hq Hh (fun i t=>U t i) hA'.le L hL).order (by omega)
end
end YM.CF.Cay
