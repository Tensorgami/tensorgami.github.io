(() => {
  const endpoint = "https://dry-term-82db.hkshin.workers.dev/track";
  const allowedHosts = new Set([
    "tensorgami.com",
    "www.tensorgami.com",
    "tensorgami.github.io",
  ]);

  const publicSite = () => {
    return (
      (window.location.protocol === "https:" || window.location.protocol === "http:") &&
      allowedHosts.has(window.location.hostname)
    );
  };

  const applyPreferenceFromQuery = () => {
    if (!publicSite()) return;

    const params = new URLSearchParams(window.location.search);
    const analytics = params.get("analytics");
    if (analytics !== "off" && analytics !== "on") return;

    try {
      if (analytics === "off") {
        window.localStorage.setItem("tensorgamiAnalyticsOptOut", "1");
      } else {
        window.localStorage.removeItem("tensorgamiAnalyticsOptOut");
      }
    } catch {
      return;
    }

    try {
      params.delete("analytics");
      const search = params.toString();
      const cleanUrl =
        window.location.pathname + (search ? `?${search}` : "") + window.location.hash;
      window.history.replaceState(null, "", cleanUrl);
    } catch {
      // The preference has already been applied; URL cleanup is only cosmetic.
    }
  };

  const optedOut = () => {
    try {
      return window.localStorage.getItem("tensorgamiAnalyticsOptOut") === "1";
    } catch {
      return false;
    }
  };

  const privacySignal = () => {
    return navigator.doNotTrack === "1" || window.doNotTrack === "1";
  };

  const send = (extra = {}) => {
    if (!publicSite()) return;
    if (optedOut() || privacySignal()) return;

    const payload = {
      event: "pageview",
      host: window.location.hostname,
      path: window.location.pathname + window.location.search,
      title: document.title || "",
      referrer: document.referrer || "",
      timezone: Intl.DateTimeFormat().resolvedOptions().timeZone || "",
      ...extra,
    };
    const body = JSON.stringify(payload);

    if (navigator.sendBeacon) {
      navigator.sendBeacon(endpoint, new Blob([body], { type: "application/json" }));
      return;
    }

    fetch(endpoint, {
      method: "POST",
      mode: "cors",
      keepalive: true,
      headers: { "Content-Type": "application/json" },
      body,
    }).catch(() => {});
  };

  applyPreferenceFromQuery();
  send();

  document.addEventListener(
    "click",
    (event) => {
      const link = event.target.closest ? event.target.closest("a[href]") : null;
      if (!link) return;

      const target = new URL(link.href, window.location.href);
      if (target.origin !== window.location.origin) return;
      if (!target.pathname.toLowerCase().endsWith(".pdf")) return;

      send({
        event: "pdf-click",
        path: target.pathname + target.search,
        title: "PDF link click",
        referrer: window.location.href,
      });
    },
    { capture: true },
  );
})();
