import YM.CF.Mir.Rule

/-! Reflection survival of the cue law. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir.Trip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (b : Trip m)
lemma cups (r : Zone) (a : Spot m) (U : Skin m B) (s : ArrayF m) : fundF m B (through B b U) (b.riseF s) r a=fundF m B U s r (shiftI b a) := by
  have hk : permits m (shiftI b a) r=(permits m a r).image (fun v=> v.map b.appoint) := by
    ext i; rw [mem_image]; constructor
    · intro hi; exact ⟨i.map b⁻¹.appoint,(wind_fit ..).mp (by rw [winding]; exact hi),winding ..⟩
    rintro ⟨j,h,rfl⟩; exact (wind_fit ..).mpr h
  unfold fundF; rw [hk,prod_image]; apply prod_congr rfl; intro l h; unfold rateF; rw [train_turn _ _ (a:=a) _ l (permits_iff.mp h).1]; rfl
  intro i _ j _ h; have he t : List.map b⁻¹.appoint (List.map b.appoint t)=t := by nth_rw 1 [show List.map b.appoint _=List.map (b⁻¹)⁻¹.appoint t by rw [inv_inv]]; exact b⁻¹.winding _
  dsimp only at h; rw [←he i,←he j,h]
lemma rows_rot (x : Cue m) (k : Index m) (v : Ballot) : update (b.oncue x) k v=b.oncue (update x (b.adv k) v) := by
  funext z; by_cases h:z=k; rw [h]; simp [oncue]; have he : b.adv z≠b.adv k := b.facesA.injective.ne h; simp [oncue,h,he]
lemma shrink_rows {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) (U : Skin m B) (f : I→ArrayF m) (r : I→Zone) (j : Row) (a : Index m) (x : Cue m) :
    priceW m B S (through B b U) (fun i=>riseF b (f i)) r j a (b.oncue x) = priceW m B S U f r j (b.adv a) x := by
  have ht (y) : draw m B S (through B b U) (fun i=>riseF b (f i)) r j a (b.oncue y)= draw m B S U f r j (b.adv a) y := by
    apply prod_congr rfl; intro i _; unfold dry; rw [show capRow (riseF b (f i)) j _ = riseF b (capRow (f i) j y) by funext z; unfold capRow riseF oncue; simp]; exact cups ..
  unfold priceW; rw [ht,limitW,limitW]; simp_rw [rows_rot,ht]
lemma water_turn (U : Skin m B) (v : Cue m) (a : Index m) : water m B (through B b U) a (b.oncue v)=water m B U (b.adv a) v := shrink_rows b _ _ (fun _=>slot m v) _ _ _ _
lemma law_turn (U : Skin m B) (v : Cue m) : law m B (through B b U) (b.oncue v)=law m B U v := by unfold law; simp_rw [water_turn]; exact Equiv.prod_comp b.facesA (fun a=>water m B U a v)
lemma cue_rev (x) : b.oncue (b⁻¹.oncue x)=x := by rw [cue_comp, inv_mul_cancel,cue_o]
def ontoC : Cue m ≃ₜ Cue m :=
  { toFun := b.oncue, invFun := b⁻¹.oncue, left_inv x := by rw [cue_comp,mul_inv_cancel,cue_o]
    right_inv x := b.cue_rev x, continuous_toFun := covo ..,continuous_invFun := covo .. }
lemma rains_p : MeasurePreserving (oncue b) (rains m) (rains m) := by
  have g := measurePreserving_piCongrLeft (α:=fun _:Index m=>Ballot) (fun _=>cloud) b.facesA.symm
  convert! g using 1
  funext x i; obtain ⟨j,rfl⟩ := b.facesA.symm.surjective i; symm; rw [MeasurableEquiv.piCongrLeft_apply_apply]; exact (congrArg x (adv_last b j)).symm
lemma rains_rev (f : Cue m→ℂ) : ∫ x, f (b.oncue x) ∂rains m=∫ x,f x ∂rains m := (b.rains_p).integral_comp b.ontoC.measurableEmbedding _
lemma pore (U : Skin m B) (x : Cue m) (v : Site (Domain m B)→E) : onPack B b (Lattice.gauge v U, partner m B v x) = (Lattice.gauge (v ∘ run B b) (through B b U), partner m B (v ∘ run B b) (oncue b x)) := by
  unfold onPack; dsimp only; rw [invert_path]; apply congrArg (fun x: Cue m=>(_,x)); funext i; unfold oncue partner; simp [addressAdv]
lemma location (v : Index m) : ((faces m v).image (adv b))=faces m (b.adv v) := by
  ext i; rw [mem_image]; constructor; rintro ⟨t,h,rfl⟩; exact mem_filter.mpr ⟨mem_univ _, (b.fits _ _).mpr (mem_filter.mp h).2⟩
  intro h; refine ⟨b⁻¹.adv i,mem_filter.mpr ⟨mem_univ _, ?_⟩,adv_last ..⟩; apply (b.fits _ _).mp; rw [adv_last]; exact (mem_filter.mp h).2
lemma chairs_rot (S : Support (Domain m B)) : (chairs m B S).image (b.adv)=chairs m B (S.image (run B b)) := by
  ext i; rw [mem_image,chaff]; constructor
  · rintro ⟨x,h,rfl⟩; obtain ⟨z,l,v,Q,K⟩ := chaff.mp h; exact ⟨_,mem_image_of_mem _ l,b.adv v,(active_turn b z v).mpr Q,(fits b x v).mpr K⟩
  rintro ⟨x,h,u,v,p⟩; obtain ⟨y,g,rfl⟩ := mem_image.mp h
  refine ⟨adv b⁻¹ i, chaff.mpr ⟨y,g,b⁻¹.adv u,(active_turn b _ _).mp ?_, (fits b _ _).mp ?_⟩,adv_last ..⟩ <;> simpa
lemma pad_rot (S : Support (Domain m B)) : (pavilion m B S).image (b.adv)=pavilion m B (S.image (run B b)) := by
  have H (b:Trip m) S i (p:i∈pavilion m B S) : b.adv i∈ pavilion m B (S.image (run B b)) := by
    obtain ⟨x,g,v,e,k⟩ := (pad_iff S i).mp p
    exact (pad_iff ..).mpr ⟨_,mem_image_of_mem _ g,b.adv v,(roomA b v _).mpr e,by unfold adv affine; rw [separation_translate,separation_signed]; exact k⟩
  ext x; rw [mem_image]; constructor; rintro ⟨i,p,rfl⟩; exact H b S _ p
  intro h; have he := H b⁻¹ _ _ h; rw [image_image] at he; rw [show run B b⁻¹ ∘ run B b=id from funext (run_back B b), image_id] at he; exact ⟨_,he,adv_last ..⟩
lemma wall_rot (S : Support (Domain m B)) : (walls m B S).image (run B b)=walls m B (S.image (run B b)) := by
  unfold walls; rw [image_union,biUnion_image]; congr 1; simp_rw [room_run]; rw [←pad_rot,image_biUnion]
end YM.CF.Mir.Trip
