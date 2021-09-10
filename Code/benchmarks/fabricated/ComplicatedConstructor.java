class ComplicatedConstructor {
	private String name;

	private String repositoryName;

	private String title;

	private String description;

	private String githubUrl;

	private String gitUrl;

	private String sshUrl;

	private String cloneUrl;

	private String[] projects;

	ComplicatedConstructor() {
		this.repositoryName = "";
		String description = "";
		if (description != null) {
			String[] split = {""};
			this.title = split[0].trim();
			this.description = (split.length > 1) ? split[1].trim() : "";
		} else {
			this.title = "";
			this.description = "";
		}
		this.githubUrl = "";
		this.gitUrl = "";
		this.sshUrl = "";
		this.cloneUrl = "";
	}
}
