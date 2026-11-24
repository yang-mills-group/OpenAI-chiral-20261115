import YM.CF.Cay.Rot
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
open Matrix AnalyticBridge.RelativeLogdet.Ink Far
section
variable {X:Support c}
def shotB(Y:ζ→ℝ)(M:ζ):= ash (Directions G f) (Y ∘ rough M) M.z
def violet(M:ζ):= rough M (-M.z)
lemma bolt_m (M:ζ): (∑ i: Bond f, arrow i M.z)= M.z:=by funext i; rw [Finset.sum_apply,sum_eq_single i]; exact Pi.single_eq_same ..; intro j _ hj; exact Pi.single_eq_of_ne hj.symm _; simp
lemma bean_m(Y:ζ→ℝ)(M:ζ): ∑ i,spring Y i M= strut (Y ∘ rough M) M.z M.z:=by unfold spring; dsimp only; rw [sum_add_distrib, ← sum_div,← map_sum,←map_sum,bolt_m]; rfl
lemma shotB_loc {Y:ζ→ℝ}(h:Virt S Y X):Virt S (shotB Y) X:=by
 intro M N p; have he:Y∘ rough M=Y∘ rough N:=funext fun i=>h (coat p (fun _ _=> rfl)); unfold shotB ash secT; rw [← bean_m,←bean_m]; have hh : (Y∘ rough M) M.z=(Y ∘ rough N) N.z:=h p
 rw [hh,he]; exact congrArg (_-·) (sum_congr rfl fun i _=>stanza h _ p)
end
variable {s C D M ε:ℝ}{i: Along S}{t:Signed}{Y: ζ → ℝ}{p:Site c}{A: Monk SU.group S}{g:Site c→SU.group.El}{R:Directions G c→ Mast G c}{m:ℕ}{K₀ L:ℝ}
def mon3(n:ℕ)(j:ℕ)(C D M β v s:ℝ):=composeCost n ((2^n*(|coupling β| * (v*C)))^j* composeCost n M s) (1/2) -- D unused
lemma peer_p(v:ℝ)(hx:‖A.z‖≤ v)(h:K.Funds S T)(ht:0<w)(hp:1000 ≤ radiusB x)(hl:0<s)(hr:s ≤ ε)(hg:n+4 ≤ r)(hy:separation p (herald S t i)+horn x l ≤ m*radiusB x)(hv:Lamp T s x A p g R m r)(hn: Ready T x)(hu:ShardIncome r x L K₀ w T A.key A.park A.V A.k)(H:∀ y:Mast G c,‖y‖<1→ Fire T x A.park A.k l s r C y)(HZ: |coupling β| * (v*C) ≤ s/2)(HF: KnotP (lava T A.park x A.k l t i) r D M ε): let U:= dense T x q d l β t i; let M'(y):=A.atop y x; let S0(y):=shotB U (M' y); let S1(y):=shotB U (violet (M' y));
 Allows n S0 0 (mon3 n 3 C D M β v s)∧ Allows n S1 0 (mon3 n 3 C D M β v s)∧ Allows n (S0 + S1) 0 (mon3 n 4 C D M β v s+ mon3 n 4 C D M β v s):=by
 intro U M' S0 S1; let Z:= latticeFieldEstimates S g; let W:=lava T A.park x A.k l t i; let P:=peer T x A.park A.k q d l β s; let Q:= fun y=> P (R y); let Y:=north T A.park s; let z:=Z A.z; have hb:‖z‖≤v:=(speed g A).trans hx
 have he:∀ᶠ y in 𝓝 0, S0 y=rill W (Y (R y)) (Q y z) ∧ S1 y=rill W (Y (R y)) (Q y (-z)):=by
    filter_upwards [rays h ht hn hp hu hv H (d:=d) (q:=q) (β:=β) hy] with y hY; let a:=Y (R y); let F:Directions G f→L[ℝ] Ark T A.park:=(Q y).comp Z; obtain ⟨hα,h𝕓⟩:=hY
    have hR: ‖a‖< ε:= by unfold a Y north; rw [Prod.norm_def,norm_smul_of_nonneg hl.le,norm_zero]; exact max_lt ((mul_lt_of_lt_one_right hl hα).trans_le hr) (hl.trans_le hr)
    have hg':= (HF.sails _ hR).smooth.of_le (show ((2:ℕ):ℕ∞ω) ≤ ↑r by exact_mod_cast (show 2 ≤ r by omega)); constructor
    · change ash _ _ _= _; rw [show U ∘ rough (M' y)=fun i=>W (a+F i) from h𝕓]; exact tuneK F A.z W a hg'
    change ash _ (U ∘ rough (M' y)) (-A.z)= _; rw [show U ∘ rough (M' y)=fun i=>W (a+ F i) from h𝕓,tuneK F (-A.z) W a hg']; rw [show F (-A.z)= Q y (-z) from congrArg (Q y) (map_neg ..)]
 let G':=mon3 n; have hz(w':Directions G f)(hw:‖w'‖≤ v): Allows n (fun i=>rill W (Y (R i)) (Q i w')) 0 (G' 3 C D M β v s)∧ Allows n (fun i=>ravel W (Y (R i)) (Q i w')) 0 (G' 4 C D M β v s):=by
    have hp:‖R 0‖<1:=hv.stage.value.trans_lt (by norm_num); have heX:= hv.stage.order (show n ≤ r by omega)
    exact ⟨(cubic W n Y _ _ _ _ (upBook H (by omega) hw hl hp hr HF.sails HZ)).comp heX,(quadT W n Y _ _ _ _ (upBook H (by omega) hw hl hp hr HF.sails HZ)).comp heX⟩
 obtain ⟨h1,h2⟩:= hz z hb; obtain ⟨h3,h4⟩:=hz (-z) (by rwa [norm_neg]); refine ⟨h1.germ (he.mono fun i h=>h.1.symm),h3.germ (he.mono fun i h=> h.2.symm),(h2.add h4).germ ?_⟩; filter_upwards [he] with i hi; rw [Pi.add_apply,hi.1,hi.2,map_neg]; exact (rplus W _ _).symm
end YM.CF.Cay
