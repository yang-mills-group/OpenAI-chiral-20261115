import YM.SU5.Regis.Hospitality
import YM.SU5.Diva.Shawl

import YM.SU5.Gleam.Innate
import YM.SU5.FiniteGaugeData.Pannier.Sketch
import YM.SU5.Fineness.Stitch
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
private lemma grows_worlds (d:Grace K R L) (x:ℝ)(t:ℕ): ∀ᶠ s in atTop, t*(radiusB (hat R.L x s))^3 ≤ R.L.val^s:=by
 let a:= billX R.L; let b(s:ℕ):= R.L.val ^ s
 let V(s):= hat R.L x s; let h:= stage_slope d x
 -- compare r^3 ≤ V at even huge s. pay arbitrary linear ≤ b
 have hz: Tendsto (fun i:ℕ=> (radiusB (V i):ℝ)^3/(V i)) atTop (𝓝 0):=by simpa only [Real.rpow_one,Function.comp_def,V] using (Work.E09.radiusB_small 1 zero_lt_one 3 |>.tendsto_div_nhds_zero).comp h
 have hf:1 < (R.L.val:ℝ):= by exact_mod_cast (show 1 < R.L.val by have t:=d.tallX; omega)
 have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hf
 have hp':Tendsto (fun i:ℕ=> (t:ℝ)* V i / (R.L.val:ℝ)^i) atTop (𝓝 0):=by
    have hh := ht.const_mul a; have hl:= tendsto_const_nhds.div_atTop (f:=fun i:ℕ=> x) (tendsto_pow_atTop_atTop_of_one_lt hf); let H := (hl.add hh).const_mul (t:ℝ); have he: Tendsto (fun i:ℕ => (t:ℝ)*(x/(R.L.val:ℝ)^i + a*((i:ℝ)/(R.L.val:ℝ)^i))) atTop (𝓝 0):=by simpa only [pow_one,mul_zero,add_zero] using H
    refine he.congr ?_; intro i; unfold V hat a; ring
 filter_upwards [h.eventually_gt_atTop (0:ℝ),hz.eventually (ge_mem_nhds zero_lt_one),hp'.eventually (ge_mem_nhds zero_lt_one)] with s w v f
 exact_mod_cast (mul_le_mul_of_nonneg_left (show (radiusB (V s):ℝ)^3 ≤ V s from ((div_le_one w).mp v)) (Nat.cast_nonneg (α:=ℝ) t)).trans ((div_le_one (by positivity)).mp f)
private lemma canopy_ville (P:Preparation): ∀ᶠ s in atTop,∀ m:Side, let N:=More (P.Ctor m s); ∃ W:Side, Odd W.val ∧ clocks.moder (radiusB (hat P.R.L P.x s)) W.val P.R.L ∧ ∃ c:Side,∃ R': Ratio c N, 2*(R'.count.val+1)< N.val ∧ R'.count=W:=by
 -- requirement x≥0 only unused? change grows_worlds
 let L:=P.R.L; let X(s):= radiusB (hat P.R.L P.x s); have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 filter_upwards [grows_worlds P.V P.x (8*L.val), (stage_slope P.V P.x).eventually (Work.E08.eventual_radiusB 1)] with s u v m N
 obtain ⟨i,p,g,w⟩:= send_width_side ht v ((show X s^3 ≤8*L.val* X s^3 from le_mul_of_one_le_left (by positivity) (by omega)).trans u)
 let W:=L^i; have he:W.val=L.val^i:=rfl
 let c:= More (P.Ctor m (s-i)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-i)*P.R.L^i by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q: Ratio c N:=⟨W, congrArg Subtype.val H⟩
 refine ⟨W, (by rw [he]; exact Odd.pow P.R.odd_side), ⟨g,w⟩, c,Q,?_,rfl⟩
 change 2*(L.val^i+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh m L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ m.property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change 8*L.val*X s^3 ≤ L.val ^s at u
 have hp: L.val^i≤ L.val*X s^3:= w
 have hl: L.val^i≥1:= one_le_pow₀ ht.le
 nlinarith only [hl,hp,u]
-- geometry import & retain paths.
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
universe l0 u0
open Regis.Head CF.Pannier.Chancel
variable {I:Type u0}[Fintype I] (A:Etch SU.group I)(a:ℝ)
abbrev museumV (s:ℕ):ℝ:= Real.sqrt (hat P.R.L P.x s) -- unused Y implicit
abbrev hatsMuseo (s i k:ℕ):ℝ:= let f:= Y.uv k-s; A.muρ P.K.top.clip (P.V.L.mood f) (P.V.L.tied f) (Real.sqrt (hat P.R.L P.x s)*coupling (gram Y s i k).beta) (More (count Y s i))
def locum(s i k:ℕ)(κ x:ℝ): Prop:=
 let M:= count Y s i; let G:=gram Y s i k; let Z:=P.V.L.H (Y.uv k - s)
 ∀ {J:Type l0}[Fintype J](o:J→Seat M)(ιι:J→Signed), Injective o → (∫ V:Pane M, Real.exp ( -(G.path.inChannels P.K.top.clip G.p G.beta V) + κ* Pannier.flakes G.p.threshold V) * Real.exp (a*A.gallery (Real.sqrt (hat P.R.L P.x s)) ιι o V) ∂prior SU.group (More M))≤ Real.exp (Fineness.gaugedBase P.L G.beta (More M) Z + x* sites M+ Fintype.card J * (a*hatsMuseo Y A s i k+ A.aftermath P.K.top.clip*a^2))
lemma museo_pilot (κ ε:ℝ)(p: ε>0) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k→ locum.{l0} Y A a s i k κ ε:=by
 let T:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a₁:=|K|; let h:= P.chart; let J:= P.L; -- P.L chart?
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le -- tune
 filter_upwards [(stage_slope P.V P.x).eventually (A.cloakB R' a P.K.top.clip P.chart P.R.L a₁ (V.L.mood 0).width hv V.W.bar (abs_nonneg K) κ (ε/2) (half_pos p)),canopy_ville P] with s q H i k ht J _ o v t₀
 let N:= count Y s i; let G:=More N; let F:=Y.uv k - s; let Gx:= gram Y s i k
 obtain ⟨W,g,t,c,r,u,hX⟩:= H (Y.ir i)
 obtain ⟨he,hT,e,f,_⟩:= prices_plot Y s i k ht
 have hV: Gx.p.threshold=temp (hat P.R.L P.x s):= he ▸ (Y.meter.boot s).1
 let Z:= P.V.L.H F; have hm:=P.V.L.roof F; let Q:=V.L.path F; have hx:T.top.clip=P.K.top.clip:=rfl
 have Hs := q W g t Gx.p Gx.beta f hV G c r u hX (V.L.tied F) (V.L.mood F) (hm.2.1 G) V.W.reserve (hm.2.2 G) (fun i=>?_) o v t₀; -- gauge align
 · have hg : ∀ V:Pane N,Gleam.angBill Q P.K.top.clip Gx.p Gx.beta κ V= Real.exp (- (Gx.path.inChannels P.K.top.clip Gx.p Gx.beta V)+κ* Pannier.flakes Gx.p.threshold V):=fun U=> by unfold Gleam.angBill; change Gx.path=Q at hT; rw [← hT]; rfl
   change (∫ V:Pane N,Gleam.angBill Q P.K.top.clip Gx.p Gx.beta κ V*Real.exp (a* A.gallery _ v o V) ∂prior SU.group (More N))≤ _ at Hs; simp_rw [hg] at Hs; exact Hs.trans_eq (congrArg Real.exp (show _=_ from (by unfold Gleam.Roof Fineness.gaugedBase; rw [Pannier.shadowLie,sites_as_price,show 2*(ε/2)=ε from (by ring)])))
 exact (YM.Fineness.stairEstimate Z P.K.width.le hm.1.2.1 i).trans (le_abs_self K)
lemma gauge_scene (ε:ℝ)(hε:0<ε)(κ:ℝ) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤ Y.uv k → let G:= gram Y s i k; let N:=count Y s i; ∀ {J:Type l0} [Fintype J](o:J→ Seat N)(ιι:J→ Signed), Injective o → ∀ (f:Orbit N→ℂ)(t:ℝ), Integrable f (city N) →
 (∀ᵐ x:Orbit N ∂city N, ‖f x‖ ≤ Real.exp (-(G.path.inChannels G.funds G.p G.beta x.1) + κ*Pannier.flakes G.p.threshold x.1 + a* A.gallery (Real.sqrt (hat P.R.L P.x s)) ιι o x.1 + t)) → (∫ x:Orbit N,‖f x‖∂city N)≤ Real.exp (Fineness.gaugedBase P.L G.beta (More N) (P.V.L.H (Y.uv k-s))+ ε*sites N+Fintype.card J *(a*hatsMuseo Y A s i k+ A.aftermath P.K.top.clip*a^2)+t):=by
 filter_upwards [museo_pilot Y A a κ ε hε] with s q i k ht G N J _ o v lQ f t h hu
 obtain ⟨g,W,e,_⟩:= prices_plot Y s i k ht
 let ℒ:=P.K.top.clip; let H:= Real.exp t; let F(U:Pane N):=angBill G.path ℒ G.p G.beta κ U * Real.exp (a * A.gallery (Real.sqrt (hat P.R.L P.x s)) v o U) * H
 let X:= prior SU.group (More N); have hf: Integrable F X:=by
    change G.path= _ at W; unfold F; rw [W]; exact (((env_ang (P.V.L.mood (Y.uv k-s))).mul (expEnv (A.museum ..) a)).integrable _).mul_const _
 let kP(x:Orbit N):= F x.1; have hL:Integrable kP (city N):= ((measurePreserving_fst (μ:=X) (ν:=depot N)).integrable_comp hf.aestronglyMeasurable).mpr hf
 apply le_trans (b:=∫ u,kP u ∂city N)
 · apply integral_mono_ae h.norm hL; filter_upwards [hu] with x t; apply t.trans; change G.funds=_ at e; rw [e,Real.exp_add,Real.exp_add]; exact le_rfl
 rw [CF.Window.usesPrior _ hf]; unfold F; rw [integral_mul_const,Real.exp_add]; exact mul_le_mul_of_nonneg_right (q i k ht o v lQ) (Real.exp_pos _).le


def rentDriven (s i k:ℕ) (h z c κ:ℝ)(H:Pane (count Y s i)→ℝ)(F:Mark (count Y s i)): Prop:=
 let Q:=gram Y s i k; let w:=room Y s i; let T:=count Y s i; ∀ x: Orbit T, Yep h (acts (star (F (x.1,w x))) (mateK _)) (changeM P.U (w x) Q.J.M) (Real.exp (trade (spar P.K.j Q.J.M (w x)) (tickA _) z +κ*flakes Q.p.threshold x.1+(c+ H x.1)))
open Branch
lemma charged_veil   (τ:ℝ) {a:ℕ}(s:ℝ)(Q:Procurement P.K.j a P.d) (c:0<z)(o:z≤1)(p:0<s)(hL:SizeCloud P.K.j s z) (hp:0≤h)(p':P.Attic)(t:Geometry P)(v:ℝ):∀ᶠ j:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → j ≤ Y.uv k → ∀ {J:Type l0} [Fintype J](o:J→ Seat (count Y j i))(ιι:J→Signed),Injective o → ∀ (F:Mark (count Y j i)) (C:ℝ),Envelope F → rentDriven Y j i k h z C v (fun x=> τ*A.gallery (museumV (P:=P) j) ιι o x) F → BrokenMark Y j i k F ≤ Real.exp ((9*s)*(sites (count Y j i)) + C + Fintype.card J*(τ*hatsMuseo Y A j i k + A.aftermath P.K.top.clip*τ^2)) :=by
 -- combination: +4 mile +2 tilt +1 gauge +1 benchmark
 obtain ⟨κ,Hk,L⟩:= earns_renewal Y Q c o s p hL
 let X:= P.W.C; obtain ⟨μ,Hμ,R⟩:= VelvetC.wisps_goal (t:=P.d) (r:=P.J.n) hp (cash_v X) P.J.ht (level_p X) p
 obtain ⟨w,hw,hl,Hw⟩:=acrobat Y p' h s p; filter_upwards [Hw, benchmarks Y s p t,L, (turnover P).eventually R,gauge_scene Y A τ s p (κ+v+μ), (turnover P).eventually (((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds p))] with j hV q HC ⟨n,hBudget⟩ hX W
 filter_upwards [HC,(count_grows Y j).eventually_ge_atTop n] with i H n0 k pC pA J₀ _ b₀ ιι hι F C pZ Hz
 let B:=gram Y j i k; let N:=count Y j i; let f:= fun (x:Orbit (count Y j i))=> letterRead (F (x.1,room Y j i x)) (Graph.recX P.U (gram Y j i k) (room Y j i) x); let g:=room Y j i; let A₀:= Graph.recX P.U B g; let V:= sites N; let D:=sod Y k j i; let T:= P.K
 let Hv:=Y.each_level i k j pC pA; have Hf: Integrable f (city N):=mark_integrable (roofage Y i j).bill pZ ((Marks.can_read _ _ _ _ Hv).smul (Complex.exp (-B.v)))
 let b:=angleFin B.J.M N T.j
 let Hκ:=b+7*s*V+C; obtain ⟨J,Tj⟩:=hV i k pA; have htY := (Y.voyage i).paths k; have Ht:= htY.paid.can.isle j; obtain ⟨hx,vB,gV,hH,h'⟩:=prices_plot Y j i k pA; have hJ:J.p.threshold=B.p.threshold:=congrArg _ Tj.shape;
 let Up(x:Orbit N):=τ*A.gallery (museumV (P:=P) j) ιι b₀ x.1; have hc:∀ᵐ x:Orbit N ∂city N, ‖f x‖≤ Real.exp (-(B.path.inChannels B.funds B.p B.beta x.1) + (κ+v+μ)*flakes B.p.threshold x.1+τ*A.gallery (museumV (P:=P) j) ιι b₀ x.1+Hκ):= by
    filter_upwards [ae_fleet (n:=N) (show Rue.IsleB SU.group J.p.threshold from (by rw [Tj.shape,hx]; exact Ht))] with x HX; -- tune
    have heX:= speck Y j i k pA; let Z:= (v*flakes B.p.threshold x.1+(C+Up x)); let D':=trade (spar T.j B.J.M (g x)) (tickA N) z; let E:=Real.exp (D'+Z); let k':=flakes B.p.threshold x.1; let R':= (4*s)*V+μ*k'
    have hm:=hBudget (roofage Y i j) w _ _ P.K.j Tj.age hw n0 W W x (Tj.tune.symm ▸ (safety Y j i k x).1 : IsStarProjection (spar T.j J.J.M (g x))); rw [←heX] at hm; let f':=F (x.1,g x); let Y':= Graph.beam J P.U g x; let b':= mateK N; have hy': Yep h (acts (star f') b') (changeM P.U (g x) B.J.M) E:=by
       specialize Hz x; unfold E Z; rw [←add_assoc]; exact Hz
    have ht := Yep.val (show Yep h _ Y' (Real.exp R'*E) from hm.2 (acts (star f') b') (changeM P.U (g x) J.J.M) E (Real.exp_pos _).le (Tj.tune.symm ▸ hy'))
    have hy : D' ≤ b+2*s*V+κ*k':= H k pA x; let a:= Graph.past J x.1; let r:= J.v - B.v; have he: Graph.recX P.U B g x= Complex.exp r • Graph.recX P.U J g x:=by
       unfold Graph.recX; rw [Tj.fare x HX, smul_smul,← Complex.exp_add,show r + -J.v= -B.v by unfold r; ring]
    change ‖letterRead f' (Graph.recX P.U B g x)‖ ≤_; rw [he, Graph.porch, map_smul, (letterRead _).map_smul_of_tower,norm_smul,Complex.norm_exp,norm_smul, Real.norm_of_nonneg (r:=a) (Real.exp_pos _|>.le)]; change _*(a*‖inner ℂ b' (acts f' Y')‖) ≤ Real.exp _; rw [← act_inner]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le)).trans; unfold E; rw [←Real.exp_add,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
    have hs:r.re≤ s*V:= (show r.re ≤ |B.v.re-J.v.re| from (by dsimp [r]; simp_rw [abs_sub_comm B.v.re]; exact le_abs_self _)).trans Tj.gown
    rw [Tj.path,Tj.shape,Tj.clock,Tj.funds]; unfold Z R' Hκ; change r.re+(-(_ : ℝ)+(( (4*s)*V+μ*k')+(D'+(v*k'+(C+Up x))))) ≤ - (_:ℝ) + (κ+v+μ)*k'+Up x+(b+7*s*V+C); linarith only [hy,hs]
 change (∫ i, ‖f i‖ ∂_)/_ ≤_;
 let μ':= Real.exp (D-s*V); let Z:= ‖vac0 P.U B g‖; let Zg:= Fintype.card J₀*(τ*hatsMuseo Y A j i k + A.aftermath P.K.top.clip*τ^2); let m:=Real.exp ((9*s)*V+C+Zg)
 have he: μ'≤Z:=q i k pC pA; have ha: Z>0:= (Real.exp_pos _).trans_le he; refine (div_le_iff₀ ha).2 ?_; refine (hX i k pA b₀ ιι hι f Hκ Hf hc).trans ((mul_le_mul_of_nonneg_left he (Real.exp_pos ((9*s)*V+C+Zg)|>.le)).trans' ?_)
 apply le_of_eq; rw [←Real.exp_add]; let Hψ:= Fineness.gaugedBase P.L B.beta (More N) (P.V.L.H (Y.uv k-j)); change Real.exp (Hψ+s*V+ Zg+Hκ)=Real.exp _; rw [show D=Hψ+b from rfl]; unfold Hκ; congr 1; unfold Zg; ring
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.gauge_scene

#print axioms YM.CF.Py.Rate.LocalLimit.Papal.charged_veil
