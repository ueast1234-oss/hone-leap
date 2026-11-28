// =========================================================
// HONE - Service Worker (GitHub Pages Subpath & Redirect-Safe)
// =========================================================

const CACHE_NAME = 'hone-cache-v50';

const ASSETS_TO_CACHE = [
  './index.html',
  './style.css',
  './app.js',
  './firebase-config.js',
  './manifest.json',
  './data/words.csv',
  './data/examples.csv',
  './data/derivatives.csv',
  './assets/icon-192.png',
  './assets/icon-512.png'
];

function cleanRedirectedResponse(res) {
  if (!res || !res.redirected) return Promise.resolve(res);
  return res.blob().then((bodyBlob) => {
    return new Response(bodyBlob, {
      status: res.status,
      statusText: res.statusText,
      headers: res.headers
    });
  });
}

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME).then(async (cache) => {
      await Promise.all(
        ASSETS_TO_CACHE.map(async (assetUrl) => {
          try {
            const netRes = await fetch(assetUrl, { redirect: 'follow', cache: 'no-cache' });
            if (netRes && netRes.ok && !netRes.redirected) {
              await cache.put(assetUrl, netRes);
            }
          } catch (err) {
            console.warn('Failed to precache asset:', assetUrl, err);
          }
        })
      );
    })
  );
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(
        keys
          .filter((key) => key !== CACHE_NAME)
          .map((key) => caches.delete(key))
      )
    ).then(() => self.clients.claim())
  );
});

self.addEventListener('fetch', (event) => {
  if (event.request.method !== 'GET') return;

  const url = new URL(event.request.url);
  if (url.origin !== self.location.origin) return;

  // Navigation requests: serve cached ./index.html offline, avoid redirected responses
  if (event.request.mode === 'navigate') {
    event.respondWith(
      fetch(event.request.url, { redirect: 'follow' })
        .then((netRes) => {
          if (netRes && netRes.status === 200 && netRes.type === 'basic' && !netRes.redirected) {
            const copy = netRes.clone();
            caches.open(CACHE_NAME).then((cache) => cache.put('./index.html', copy));
            return netRes;
          }
          return cleanRedirectedResponse(netRes);
        })
        .catch(() => caches.match('./index.html'))
    );
    return;
  }

  event.respondWith(
    caches.match(event.request).then((cached) => {
      if (cached && !cached.redirected) {
        return cached;
      }
      return fetch(event.request.url, { redirect: 'follow' })
        .then((netRes) => {
          if (!netRes || netRes.status !== 200 || netRes.type !== 'basic') {
            return cleanRedirectedResponse(netRes);
          }
          if (!netRes.redirected) {
            const copy = netRes.clone();
            caches.open(CACHE_NAME).then((cache) => cache.put(event.request, copy));
            return netRes;
          }
          return cleanRedirectedResponse(netRes);
        })
        .catch(() => (cached && !cached.redirected ? cached : Response.error()));
    })
  );
});
