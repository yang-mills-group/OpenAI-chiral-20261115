import GaugeFieldConstruction.LiftBeforeΛL
/-!
 # Absolute sweeps give local determination in real time as well.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Mink MeasureTheory Analysis Kernel Complex Metric Distribution
open scoped BigOperators Topology ContDiff InnerProductSpace
open Complex
variable {n:ℕ}
variable {G:Gauge}{L:Register G}{S:Table L}{Y Z:Surface S}{D:∀ i,Blanket i}{F T:Waves S}{A:Y.Aurora D}{B:Z.Aurora D}
variable (e:A.FullBody F)(p:B.FullBody T)
variable (D':Blanket n)(X:Distn (Points n))(f:Joint n) (h:HasCompactSupport (f:Points n→ℂ))
local notation3 "CUPΛ"=> ({z:ℂ|0≤z.im}: Set ℂ)
local notation3 "HUPΛ"=> ({z:ℂ|0<z.im}: Set ℂ)
abbrev terrainΛL (x:Points n)(U:Set (Points n)): Set (Points n):= (fun y=>y - x)⁻¹' U
lemma OpenTerrainΛL (x:Points n)(U:Set (Points n))(h:IsOpen U):IsOpen (terrainΛL x U):= h.preimage (continuous_id.sub continuous_const)
lemma AheadWildΛL (u:Points n): tsupport (Probe.ahead u f)⊆ terrainΛL u (tsupport f):=tsupport_comp_subset_preimage ⇑f (show Continuous (fun x:Points n=> x-u) from continuous_id.sub continuous_const)
lemma AheadBabyΛL (x:Points n): Probe.ahead x (Probe.ahead (-x) f)=f :=by ext1 k; simp
include h in
lemma AheadSmΛL (x:Points n): HasCompactSupport (Probe.ahead x f :Points n→ ℂ):=by
 have hx := (h.image (show Continuous (fun z=> z+x) from continuous_id.add continuous_const))
 apply hx.of_isClosed_subset (isClosed_tsupport _) (fun z hz=>?_); refine ⟨z-x,AheadWildΛL f _ hz,by simp⟩
variable {v:Points n}(hv:v∈fields n)(V V':Fin n→ S.Union)
variable (hA:Bid.cones Y)(hB:Bid.cones Z)
variable (U:Set (Points n))(o:IsOpen U)
local notation "Xζ"=> Y.W n V-Z.W n V'
include hA hB hv e p o
lemma SeedWΛL (u:IsVanishingOn (Xζ) U)(t:ℝ): IsVanishingOn (Xζ) (terrainΛL (t • v) U):=by
 apply (Distn.from_compact (Xζ)).2; intro f W h
 let x:= t • v; let g:= Probe.ahead (-x) f; have he: Probe.ahead x g=f:= AheadBabyΛL ..
 have hU:tsupport g⊆U:= by
    intro i p; have ht:= W (show i- -x∈ tsupport f from AheadWildΛL f _ p); change i- -x-x∈U at ht; simpa using ht
 have hc: HasCompactSupport (g:Points n→ℂ):= AheadSmΛL f h _
 let J:= LiftBeforeΛL (D n) (Y.W n V) g v-LiftBeforeΛL (D n) (Z.W n V') g v; have hz(r:ℝ): J (r:ℂ)= (Xζ) (Probe.ahead (r • v) g):=by
    simp only [J, Pi.sub_apply, LiftBeforeΛL,HullAheadΛL,ofReal_im,ofReal_re,zero_smul,(D n).flatD (Work.C12.answer _ (Work.C10.answer n) _) (hA n V), (D n).flatD (Work.C12.answer _ (Work.C10.answer n) _) (hB n V')]; rfl
 have q:EqOn J 0 CUPΛ:=SweepΛL ((VBefΛL (D n) (Y.W n V) g hv).sub (VBefΛL (D n) (Z.W n V') g hv)) ((analyticBeforeΛL e g hc hv V).sub (analyticBeforeΛL p g hc hv V')) (by
    let F(x:ℝ×Points n):= x.2+x.1 • v
    have hw:∀ᶠ r in 𝓝 (0:ℝ),∀ j∈tsupport g,F (r,j)∈U :=hc.eventually_forall_of_forall_eventually (fun i hi=> (o.preimage (show Continuous F from continuous_snd.add (continuous_fst.smul continuous_const))).mem_nhds (show (0,i) ∈ F⁻¹' U from show i+(0:ℝ) • v∈U from by simpa using hU hi))
    filter_upwards [hw] with r hr; change J (r:ℂ)=0; rw [hz]; apply u; intro i hi; have hf:=hr (i-r • v) (AheadWildΛL g _ hi); change _+ r • v∈U at hf; simpa using hf)
 rw [← he,←hz t]; exact q (show (t:ℂ)∈CUPΛ from by simp)
-- All translates reachable in two steps
omit hv
lemma FullWΛL (u:IsVanishingOn (Xζ) U)(x: Points n): IsVanishingOn (Xζ) (terrainΛL x U):=by
 let a:Points n:= dawn (rate n); have ha:a∈fields n:= etched ΛProfileL
 have he:Continuous (fun t:ℝ=> a+t • x):=continuous_const.add (continuous_id.smul continuous_const)
 have h:∀ᶠ t in 𝓝[>] (0:ℝ), a+t • x∈fields n:= ((he.continuousAt.tendsto (x:=0)).mono_left nhdsWithin_le_nhds).eventually ((smooth_fields n).mem_nhds (show a + (0:ℝ) • x ∈ fields n from by simpa using ha))
 obtain ⟨t,r,H⟩:= (h.and self_mem_nhdsWithin).exists
 have hx:t≠0:=(show 0<t from H).ne'; let i:=(-t⁻¹) • a; let j:=t⁻¹ • (a+t • x); have hz:j+i=x:=by unfold j i; rw [smul_add,smul_smul,inv_mul_cancel₀ hx,one_smul,neg_smul]; abel
 have hg:= SeedWΛL e p ha V V' hA hB U o u (-t⁻¹)
 have he:= SeedWΛL e p r V V' hA hB (terrainΛL i U) (OpenTerrainΛL i U o) hg t⁻¹
 rw [show terrainΛL x U=terrainΛL j (terrainΛL i U) from ?_]; exact he
 ext b; change b-x∈U↔ b-j-i∈U; rw [sub_sub, hz]
lemma ΘDawnEarthΛL (q:U.Nonempty)(u:∀ f:Joint n, tsupport f⊆U→ HasCompactSupport ⇑f → Y.W n V f=Z.W n V' f): Y.W n V=Z.W n V':=by
 have h:IsVanishingOn (Xζ) U:=(Distn.from_compact (Xζ)).2 (fun x e a=> sub_eq_zero.mpr (u x e a))
 obtain ⟨x,r⟩:=q
 have he: dsupport (Xζ)⊆∅:=by
    intro l hp; have hu:l∈terrainΛL (l-x) U:=by change l - (l-x)∈ U; simpa using r
    exact absurd (FullWΛL e p V V' hA hB U o h (l-x)) ((mem_dsupport_iff_not_isVanishingOn l).mp hp _ hu (OpenTerrainΛL _ _ o)) -- tune shadow p
 have hu:= (Distn.due (Xζ) ∅ isClosed_empty).1 he
 apply sub_eq_zero.mp; ext1 i; exact hu i (by simp)
#print axioms ΘDawnEarthΛL
end YM.NSF.Boundary
end
