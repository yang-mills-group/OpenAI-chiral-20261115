import YM.SU5.Aria.Miasma
-- possibly add C* etc
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Metric Filter
open scoped Topology
open CF.Buffered.Afterglow.Tower.Aria (firmly)
variable {H:Hilbert}{I:Type*}{l:Filter I}{a b:I→H.Op}{x y:H.Op}
/-! Stock for operators on a bundled Hilbert space. Rather than discerning
metrizability, Baire, uniform bounds etc on the strong topologies, record
direct bounded strong operator convergence with adjoints at a given filter. -/
structure BSOT (a:I→H.Op)(l:Filter I)(x:H.Op) : Prop where
 ceiling: ∃ C:ℝ,0≤ C∧ ∀ᶠ i in l, ‖a i‖ ≤ C
 showAt: ∀ u:H, Tendsto (fun i=>a i u) l (𝓝 (x u))
 starAt: ∀ u:H, Tendsto (fun i=>star (a i) u) l (𝓝 (star x u))

namespace BSOT
variable {u:H}{v:I→H}
lemma apply' (p:BSOT a l x)(q:Tendsto v l (𝓝 u)): Tendsto (fun i=>a i (v i)) l (𝓝 (x u)):=by
 obtain ⟨C,h,e⟩:= p.ceiling; exact firmly a h e (p.showAt u) q
lemma dagger (p:BSOT a l x): BSOT (fun i=>star (a i)) l (star x):=by
 refine ⟨?_,p.starAt,?_⟩
 · obtain ⟨C,u,v⟩:= p.ceiling; exact ⟨C,u,v.mono fun i q=> (norm_star (a i)).trans_le q⟩
 simp only [star_star]; exact p.showAt
lemma unique [NeBot l] (p:BSOT a l x)(h:BSOT a l y):x=y:= by ext v; exact tendsto_nhds_unique (p.showAt v) (h.showAt v)
lemma consult [NeBot l] (p:BSOT a l x) {C:ℝ}(h:0≤C)(t:∀ᶠ i in l,‖a i‖ ≤ C): ‖x‖≤ C:=by
 refine x.opNorm_le_bound h fun u=> le_of_tendsto (p.showAt u).norm ?_
 exact t.mono fun i v=> (a i).le_of_opNorm_le v u
lemma visit (p:BSOT a l x){J:Type*}{k:Filter J}{f:J→I}(h:Tendsto f k l):BSOT (fun i=>a (f i)) k x:=by
 obtain ⟨C,u,v⟩:=p.ceiling
 exact ⟨⟨C,u,h.eventually v⟩,fun _=>(p.showAt _).comp h,fun _=>(p.starAt _).comp h⟩
lemma congr' (p:BSOT a l x)(h:a=ᶠ[l] b):BSOT b l x:=by
 obtain ⟨C,u,v⟩:=p.ceiling
 exact ⟨⟨C,u,(h.and v).mono fun _ z=>(congrArg norm z.1.symm).trans_le z.2⟩,
  fun i=>(p.showAt i).congr' (h.mono fun _ z=> congrArg (fun x:H.Op=>x i) z),
  fun i=>(p.starAt i).congr' (h.mono fun _ z=>congrArg (fun x:H.Op=>star x i) z)⟩
lemma fromNorm (p:Tendsto a l (𝓝 x)):BSOT a l x:=by
 let C:=‖x‖+1
 let L:=ContinuousLinearMap.apply ℂ H (E:=H)
 exact ⟨⟨C,by unfold C;positivity, p.norm.eventually (ge_mem_nhds (show ‖x‖<C from lt_add_one _))⟩,
   fun u=>((L u).continuous.tendsto x).comp p, fun u=>((L u).continuous.tendsto (star x)).comp p.star⟩
lemma stay (x:H.Op):BSOT (fun _:I=>x) l x:= fromNorm tendsto_const_nhds

lemma mul (p:BSOT a l x)(q:BSOT b l y):BSOT (fun i=>a i*b i) l (x*y):=by
 obtain ⟨C,v,h⟩:= p.ceiling; obtain ⟨D,r,u⟩:= q.ceiling
 refine ⟨⟨C*D,by positivity,(h.and u).mono fun i z=>(norm_mul_le ..).trans (mul_le_mul z.1 z.2 (norm_nonneg _) v)⟩,
   fun i=>p.apply' (q.showAt i),?_⟩
 intro i; simp only [star_mul]; exact q.dagger.apply' (p.starAt i)
lemma add (p:BSOT a l x)(q:BSOT b l y):BSOT (fun i=>a i+b i) l (x+y):=by
 obtain ⟨C,v,h⟩:= p.ceiling; obtain ⟨D,r,u⟩:= q.ceiling
 refine ⟨⟨C+D,by positivity,(h.and u).mono fun i z=>(norm_add_le ..).trans (add_le_add z.1 z.2)⟩,
   fun i=>(p.showAt i).add (q.showAt i),?_⟩
 intro i; simp only [star_add]; exact (p.starAt i).add (q.starAt i)
lemma sub (p:BSOT a l x)(q:BSOT b l y):BSOT (fun i=>a i-b i) l (x-y):=by
 obtain ⟨C,v,h⟩:= p.ceiling; obtain ⟨D,r,u⟩:= q.ceiling
 refine ⟨⟨C+D,by positivity,(h.and u).mono fun i z=>(norm_sub_le ..).trans (add_le_add z.1 z.2)⟩,
   fun i=>(p.showAt i).sub (q.showAt i),?_⟩
 intro i; simp only [star_sub]; exact (p.starAt i).sub (q.starAt i)
lemma scale {r:ℂ}{z:I→ℂ} (p:BSOT a l x)(q:Tendsto z l (𝓝 r)):BSOT (fun i=>z i•a i) l (r•x):=by
 obtain ⟨C,v,h⟩:=p.ceiling; let D:=‖r‖+1; have hd: 0≤D:= by unfold D; positivity
 have u:=q.norm.eventually (ge_mem_nhds (show ‖r‖<D from lt_add_one _))
 refine ⟨⟨D*C,by positivity, (u.and h).mono fun i t=>(norm_smul ..).trans_le (mul_le_mul t.1 t.2 (norm_nonneg _) hd)⟩,
  fun i=>q.smul (p.showAt i),?_⟩
 intro i; simp only [star_smul]; exact q.star.smul (p.starAt i)
lemma squeeze' (p:BSOT a l x){d:I→ℝ}(q: Tendsto d l (𝓝 0))(h:∀ᶠ i in l, ‖b i-a i‖ ≤ d i):BSOT b l x:=by
 have ht:BSOT (fun i=>b i-a i) l (0:H.Op):=fromNorm (by
   rw [tendsto_iff_norm_sub_tendsto_zero]; simp only [sub_zero]
   exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) h q)
 have u:=ht.add p; simpa using u
end BSOT
end YM
