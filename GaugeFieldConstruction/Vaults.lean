import GaugeFieldConstruction.Virgin
/-
The actual spatial-jet indices hit the full real Gem and the first Maxwell-Live slot.
Proof avoids Fourier positivity on a tight time aperture.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 40000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht.Vesper
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp Conj
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
open HopeC CF.Buffered CF.Buffered.Lifted FlightFlux Fluxim TableF TableF.Lenten Layout Shield Wilson Raw
open U1 Gauge97
abbrev WaveL:= {x:S3 × SayL// ¬ (x.1=2 ∧ x.2.2=2)}
def crumbU :liveD →ₗ[ℝ] (WaveL→ℝ) where
 toFun A i:=let (u,v,z):=i.val; A.val.val u.castSucc (pipeL v z).1 (pipeL v z).2
 map_add' a b:=rfl
 map_smul' r u:=rfl
lemma diags (D:Sut)(e:D∈liveD) (i:Axis) : D.val 0 i 0+D.val 1 i 1 +D.val 2 i 2+D.val 3 i 3=0:=by
 rw [← Fin.sum_univ_four (fun j:Axis=> D.val j i j)]; exact congrFun (show breezeD D=0 from e) i
lemma crumb_s : Injective crumbU:=by
 suffices hx: ∀ D:liveD, crumbU D=0 → D=0 by
    intro D E p; suffices e:D-E=0 from sub_eq_zero.mp e; apply hx; rw [show crumbU (D-E)=crumbU D - crumbU E from rfl,p,sub_self]
 intro D H; change D=0; let X:=D.val; have he(i:WaveL): crumbU D i=0:=congrFun (show crumbU D=0 from H) i; let K(x:Axis):Gem:= ⟨D.val.val x,D.val.property.1 x⟩
 have hc(p:S3)(b:Bool)(q:S3)(r: ¬ (p=2 ∧ q=2)): (K p.castSucc).val (pipeL b q).1 (pipeL b q).2=0:= he ⟨(p,b,q),r⟩
 have hx(b:Bool): (K (2:Axis)).val (pipeL b 2).1 (pipeL b 2).2=0:=by
    have hg: X.val 0 3 0=0:=hc 0 false 0 (by decide); have hh:X.val 1 3 1=0:=hc 1 false 1 (by decide); have hv:X.val 0 1 2=0:=hc 0 true 0 (by decide); have hz:X.val 1 2 0=0:=hc 1 true 1 (by decide)
    cases b; · change X.val 2 3 2=0; have he:=diags X D.property 3; rw [hg,hh,zero_add,F_slot0 X 3 3,add_zero,zero_add] at he; exact he
    change X.val 2 0 1=0; have he:= X.property.2 0 1 2; rw [hv,hz,zero_add,zero_add] at he; exact he
 have hw(i:S3): K i.castSucc =0:=by
    refine (wick_G _).2 (fun b a=>?_); by_cases p:i=2 ∧ a=2; · rcases p with ⟨rfl,rfl⟩; exact hx b
    exact hc i b a p
 have hz(i:S3)(x y:Axis): X.val i.castSucc x y=0:=congrArg (fun v:Gem=>v.val x y) (hw i)
 have hy: K 3=0:=by
    refine (wick_G _).2 fun b a=>?_ ; cases b
    · change X.val 3 3 a.castSucc=0; have he:=diags X D.property a.castSucc; rw [F_neg X 3 3 a.castSucc, ← neg_zero]; apply congrArg
      rw [show (0:Axis)= (0:S3).castSucc from rfl,show (1:Axis)= (1:S3).castSucc from rfl,show (2:Axis)=(2:S3).castSucc from rfl] at he; simp_rw [hz,zero_add] at he; exact he
    change X.val 3 (cw a).castSucc (ccw a).castSucc=0; have he:= X.property.2 3 (cw a).castSucc (ccw a).castSucc; rw [hz,hz, add_zero,add_zero] at he; exact he
 apply Subtype.ext; apply Subtype.ext; funext i j k; change X.val i j k=0; refine Fin.lastCases (i:=i) ?_ fun v=> hz v j k; exact congrArg (fun v: Gem=> v.val j k) hy
def wallU(i:WaveL): GIndex:= (i.val.2.1,⟨(i.val.2.2,bump i.val.1 0), by
   rintro e; have h:i.val.1≠2 := fun p=> i.property ⟨p,e⟩; exact (show ∀ a:S3, a≠2 → (bump a 0).2.2=0 from by decide) i.val.1 h⟩)
lemma whamU(i:WaveL): Gder i.val.1.castSucc (F (pipeL i.val.2.1 i.val.2.2).1 (pipeL i.val.2.1 i.val.2.2).2)= ket (wallU i):=by rw [wham,Gspace,Gshift,on_ket]; exact picked_G (wallU i) -- tune
lemma wall_v : Injective wallU := by
 intro i j p; apply Subtype.ext; apply Prod.ext _ (Prod.ext _ _)
 · exact (show ∀ i j:S3,bump i 0=bump j 0→i=j from by decide) _ _ (congrArg (fun i:GIndex=> i.2.val.2) p)
 · exact congrArg (fun b:GIndex=> b.1) p
 exact congrArg (fun b:GIndex=> b.2.val.1) p
abbrev EWash (i:WaveL): liveD:=⟨E_D (wallU i),no_fee _⟩
lemma burstU (i j:WaveL): crumbU (EWash j) i= if (i=j) then 1 else 0:=by
 change (((Gder _ (F (pipeL i.val.2.1 i.val.2.2).1 (pipeL i.val.2.1 i.val.2.2).2)) (wallU j))).re= _; rw [show Gder _ _=_ from whamU i]; by_cases p:i=j; · subst i; simp [ket]
 simp [ket,Finsupp.single_apply,p,wall_v.ne p, wall_v.ne (Ne.symm p)] -- tune
lemma bead_w (A: Sut)(h:A∈ liveD): A=∑ i:WaveL,crumbU ⟨A,h⟩ i • (EWash i).val:=by
 let K:liveD:=⟨A,h⟩; have hp: K= ∑ i:WaveL,crumbU K i • EWash i:=by
    apply crumb_s; rw [map_sum]; ext1 i; simp_rw [Finset.sum_apply, map_smul, Pi.smul_apply,burstU]; simp
 exact (congrArg Subtype.val hp).trans (by simp; try rfl)
-- silence for opposite cuts. via Injective. primitive ∈live.
lemma partedD (i:WaveL): E_G (wallU i)=0:=by
 refine (wick_G _).2 (fun b a=>?_); change ((F _ _) _).re= _ -- placeholder?
 rw [show F _ _=_ from wham b a]; have he:winkL b a ≠ wallU i:=by
    intro h; have hx: bump i.val.1 0=0:=congrArg (fun i:GIndex=> i.2.val.2) h.symm
    exact (show ∀ k:S3,bump k 0 ≠ 0 from by decide) _ hx
 simp [ket,Finsupp.single_apply,he,Ne.symm he]
lemma partedE (i:SayL) : E_D (winkL i.1 i.2)=0:=by
 let a:= winkL i.1 i.2; let V:liveD:=⟨E_D a, no_fee _⟩; have he: V=0:=by
    apply crumb_s; rw [map_zero]; ext1 j; change ((Gder j.val.1.castSucc (F _ _)) a).re= _; rw [show Gder _ _=_ from whamU j]; have h: a≠wallU j:=fun h=>(show ∀ k:S3,bump k 0≠0 from by decide) _ (congrArg (fun x:GIndex=>x.2.val.2) h.symm); simp [ket,Finsupp.single_apply,h,Ne.symm h] -- tune
 exact congrArg (fun a:liveD=> a.val) he
end YM.GaugeFieldConstruction.Wick.Yacht.Vesper
end
